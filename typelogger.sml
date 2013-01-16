signature TYPE_LOGGER =
sig
  val analyzeAst : Ast.dec -> unit
end

structure TypeLogger : TYPE_LOGGER = 
struct
  structure A = Ast

  structure StringSet = ListSetFn(struct 
                                   type ord_key = string 
                                   val compare = String.compare 
                                 end) 

  exception HashMissEx

  (* TODO: Refractor FileLogger *)
  
  fun fileLogger (fname:string):(TextIO.outstream * (string -> unit)) =
    let
      val outs = TextIO.openOut fname
    in
      (outs,(fn str => TextIO.output(outs,str)))
    end

  val logger = ref (Control_Print.say)

  fun say str = 
    let
      val f = !logger
    in
      f str
    end

  datatype absty = VarTy of string | ArrowTy of string list * string list | BaseTy of string | TupleTy of absty list


  fun printSymbol (Symbol.SYMBOL(w,valname)) = say (valname)

  fun symbolToName (Symbol.SYMBOL(w,valname)) = valname

  fun abstractArrows atypelist = (List.map 
    (
      fn(aty)=> case aty of
          ArrowTy _ => VarTy "'a"
        | _ => aty
    ) atypelist
  )

  fun flattenTuples (atypelist: absty list) : absty list = case atypelist of
      [] => []
    | aty::atys => (case aty of
          TupleTy alist => alist@(flattenTuples atys)
        | _ => aty::(flattenTuples atys)
        )

  fun aTyToString aty = case aty of
      VarTy s => s
    | BaseTy s => s
    | ArrowTy (l,s) => "("^(String.concatWith "->" l)^"->"^( "("^(String.concatWith "," s)^")" )^")"
    | TupleTy absl => 
        let
          val l = List.map (fn aty => (aTyToString aty)) absl
        in
          "("^(String.concatWith "," l)^")"
        end

  fun analyzeType (ty:A.ty):absty = case ty of
      A.VarTy tyvar => VarTy "'a"
    | A.ConTy(slist,tlist) => 
      let
        val tyconstr = (List.foldl 
          (
            fn(sym,namespace) =>
              if namespace = "" then
                symbolToName sym
              else
                namespace^"."^(symbolToName sym)
          ) "" slist
        )
        val argslist = (List.map 
          (
            fn(t) => 
              (analyzeType (t))
          ) tlist
        )
      in
        if(tyconstr = "->") then
          let
            val (tyargslist,tyreslist) = 
              let
                val n = (length argslist) - 1
                val funargs = flattenTuples (List.take(argslist,n))
                val funres = List.nth(argslist,n)
                val (resfunargs,resfunres) = (case funres of
                    ArrowTy (l,reslist) => ((List.map (fn s => BaseTy s) l),
                      (List.map (fn res => BaseTy res) reslist))
                  | TupleTy abslist => ([],abslist)
                  | _ => ([],[funres])
                )
              in
                ((abstractArrows (funargs @ resfunargs)),resfunres) (* Bug: arrows filtered from ((t->t')->t'') list *)
              end
            val funargsstrs = List.map (fn(tyarg) => aTyToString tyarg) tyargslist
            val funresstr = List.map (fn(tyarg) => aTyToString tyarg) tyreslist
          in
            ArrowTy (funargsstrs,funresstr)
          end
        else
          let
            val tyargsstrs = List.map (fn(tyarg) => aTyToString tyarg) argslist
          in
            BaseTy (String.concatWith " " (tyargsstrs@[tyconstr]))
          end
      end
    | A.MarkTy(ty,region) => analyzeType ty
    | A.TupleTy tylist => 
      let
        val atylist = List.map (fn ty => (analyzeType ty)) tylist
      in
        TupleTy (flattenTuples atylist) (* (a,(b,c)) --> (a,b,c) *)
      end
    | _ => VarTy "'a"

  fun analyzeValType (v,t) = (printSymbol v; say (" : "^(aTyToString(analyzeType t))^"\n"))

  fun listIntersection (alist,blist) = (
    let
      val emptySet = StringSet.empty
      val s1 = StringSet.addList (emptySet,alist)
      val s2 = StringSet.addList (emptySet,blist)
      val xn = StringSet.intersection (s1,s2)
      val xnlist = StringSet.listItems xn
    in
      xnlist
    end
  )

  fun inductFCandidates spec hash = (
    let
      fun f stpairlist hash = 
        List.foldl
          (fn ((s,ty),hash) => (
            let
              val fnname = symbolToName s
              val (ArrowTy (argtys,restys)) = analyzeType ty
              val xn = listIntersection (argtys,restys)
              val emptySet = StringSet.empty
            in
              List.foldl
                (fn (aty,hash) => (
                  let
                    val set = ((HashTable.lookup hash aty) handle HashMissEx => emptySet )
                    val newset = StringSet.add (set,fnname^"(F)")
                    val _ = HashTable.insert hash (aty,newset)
                  in
                    hash
                  end
                ))
                hash
                xn
              (* end fold *)
            end
          ))
          hash
          stpairlist
        (* end fold *)
    in
      case spec of
          A.ValSpec stpairlist => f stpairlist hash
        | A.MarkSpec (spec,_) => inductFCandidates spec hash
        | _ => hash
    end
  )

  fun inductGCandidates spec hash = (
    let
      fun g stpairlist hash =
        List.foldl
          (fn ((s,ty),hash) => (
            let
              val fnname = symbolToName s
              val (ArrowTy (argtys,restys)) = analyzeType ty
            in
              List.foldl
                (fn (aty,hash) => (
                  let
                    val set = ((HashTable.lookup hash aty) handle HashMissEx => (StringSet.empty) )
                  in
                    if (StringSet.isEmpty set) then
                      hash
                    else
                      let
                        val newset = StringSet.add (set,fnname^"(G)")
                        val _ = HashTable.insert hash (aty,newset)
                      in
                        hash
                      end
                  end
                ))
                hash
                argtys
              (* end fold *)
            end
          ))
          hash
          stpairlist
        (* end fold *)
    in
      case spec of
          A.ValSpec stpairlist => g stpairlist hash
        | A.MarkSpec (spec,_) => inductGCandidates spec hash
        | _ => hash
    end
  )

  fun analyzeSpecList speclist =
    let
      val hash_fn = HashString.hashString
      val cmp_fn = (op =)
      val hash = HashTable.mkTable(hash_fn,cmp_fn) (23,HashMissEx)
      val tytblF = (
        List.foldl
          (fn (spec,hash) => (
            inductFCandidates spec hash
          ))
          hash
          speclist
        (*end fold*)
      )
      val tytblFG = (
        List.foldl
          (fn (spec,hash) => (
            inductGCandidates spec hash
          ))
          tytblF
          speclist
        (*end fold*)
      )
    in
      tytblFG
    end

  fun printFGGroups hash = (
    let
      val tysetpairs = HashTable.listItemsi hash
    in
      List.foldl
        (fn ((aty,set),_) => (
          say ("[Group("^aty^") : "^(String.concatWith ", " (StringSet.listItems set))^"]\n") 
        ))
        ()
        tysetpairs
      (*end fold*)
    end
  )

  fun analyzeSigExp sigex = case sigex of
      A.AugSig(sigex,speclist) => analyzeSigExp sigex (*Only analyze base sig specs*)
    | A.MarkSig(sigex,region) => analyzeSigExp sigex
    | A.VarSig _ => ()
    | A.BaseSig speclist => printFGGroups (analyzeSpecList speclist)

  fun analyzeSigDec sigdec = case sigdec of
      A.Sigb {name,def} => 
        let
          val signame = symbolToName name
          val (outs,f) = fileLogger ("annots/"^signame^".annot") 
        in
          logger := f;
          analyzeSigExp def;
          logger := Control_Print.say;
          TextIO.closeOut outs
        end

    | A.MarkSigb(sigb,region) => analyzeSigDec sigb

  fun analyzeAst ast = case ast of
      A.SigDec slist => List.foldl (fn(sigdec,_) => analyzeSigDec sigdec) () slist
	  | A.MarkDec(dec,region) => analyzeAst dec
    | _ => () (* We only care about Signature defs *)
  
end

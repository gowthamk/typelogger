signature TYPE_LOGGER =
sig
  val analyzeAst : Ast.dec -> unit
end

structure TypeLogger : TYPE_LOGGER = 
struct
  structure A = Ast
  val say = Control_Print.say

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

  fun analyzeSpec spec = case spec of
      A.ValSpec stpairlist => List.foldl (fn((s,t),_)=>(analyzeValType (s,t))) () stpairlist
    | _ => ()

  fun analyzeSigExp sigex = case sigex of
      A.AugSig(sigex,speclist) => analyzeSigExp sigex (*Only analyze base sig specs*)
    | A.MarkSig(sigex,region) => analyzeSigExp sigex
    | A.VarSig _ => ()
    | A.BaseSig speclist => List.foldl (fn(spec,_) => analyzeSpec spec) () speclist

  fun analyzeSigDec sigdec = case sigdec of
      A.Sigb {name,def} => analyzeSigExp def
    | A.MarkSigb(sigb,region) => analyzeSigDec sigb

  fun analyzeAst ast = case ast of
      A.SigDec slist => List.foldl (fn(sigdec,_) => analyzeSigDec sigdec) () slist
	  | A.MarkDec(dec,region) => analyzeAst dec
    | _ => say "[analyzeAst: Got non SigDec]\n" (* We only care about Signature defs *)
  
end

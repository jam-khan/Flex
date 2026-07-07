import Lean
import Flex.PA.Qualifier
import Flex.PA.Instantiation
import Flex.PA.Check

open Lean Meta

@[qualif] def _test_q_le (a : Int) (b : Int) : Prop := a ≤ b
@[qualif] def _test_q_pos (v : Int) : Prop := 0 ≤ v

#eval show MetaM Unit from do
  let qs ← getQualifiers
  for q in qs do
    let ty ← inferType q
    let ci ← getConstInfo q.constName!
    IO.println s!" {q} : {← ppExpr ty}"
    if let some val := ci.value? then
      IO.println s!"    = {← ppExpr val}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let intTy := mkConst ``Int
  let kvarParamTypes : List Expr := [intTy, intTy, intTy, intTy]
  for q in (← getQualifiers) do
    let insts ← instantiateQualifier q kvarParamTypes
    IO.println s!"{q.constName!}: {insts.size} instantiations"
    for (qExpr, idxs) in insts do
      -- demo: substitute Int.ofNat <slot index> for each slot
      let actualArgs := idxs.toArray.map (fun i => mkApp (mkConst ``Int.ofNat) (mkNatLit i))
      let applied ← Lean.Meta.mkAppM' qExpr actualArgs
      IO.println s!"  {← ppExpr qExpr} @ slots {idxs}  =  {← ppExpr applied}"

run_cmd Lean.Elab.Command.liftTermElabM do
  let ok1 ← checkExprVC (mkConst ``True)
  IO.println s!"True                              → {ok1}   (expect true)"
  let ok2 ← checkExprVC (mkConst ``False)
  IO.println s!"False                             → {ok2}   (expect false)"
  let p3 ← Lean.Elab.Term.elabTerm
    (← `(∀ (x : Int), x + 0 = x)) none
  let ok3 ← checkExprVC p3
  IO.println s!"∀ x : Int, x + 0 = x              → {ok3}   (expect true)"
  let p4 ← Lean.Elab.Term.elabTerm
    (← `(∀ (i n : Int), i > 1 → i ≤ n → i < n + 1)) none
  let ok4 ← checkExprVC p4
  IO.println s!"∀ i n, i > 1 → i ≤ n → i < n + 1  → {ok4}   (expect true)"
  let p5 ← Lean.Elab.Term.elabTerm
    (← `(∀ (x : Int), x = x + 1)) none
  let ok5 ← checkExprVC p5
  IO.println s!"∀ x : Int, x = x + 1              → {ok5}   (expect false)"

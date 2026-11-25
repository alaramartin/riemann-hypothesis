module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.NotAboveTransGenSelf

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace CompanionTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem linkP : LinkP k := PositivityTheory.Exh.linkP

private def Above (a b : IrrGL (k := k)) : Prop := 0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ)

private theorem above_transGen {a b : IrrGL (k := k)} (H : Relation.TransGen Above a b) :
    0 < a.1 ∧ ∃ j : ℕ, 0 < j ∧ a = b.nu (j : ℕ) := by
  induction H with
  | single H => exact H
  | tail _ H ih =>
    obtain ⟨ha, i, hi, e⟩ := ih
    obtain ⟨-, j, hj, e'⟩ := H
    exact ⟨ha, i + j, by omega, by rw [e, e', IrrGL.nu_nu, Nat.cast_add, add_comm]⟩

private theorem not_above_transGen_self (a : IrrGL (k := k)) : ¬ Relation.TransGen Above a a := fun H => by
  obtain ⟨ha, j, hj, e⟩ := above_transGen H
  have : a.nu ((0 : ℕ) : ℂ) = a.nu ((j : ℕ) : ℂ) := by simpa using e
  exact hj.ne ((IrrGL.nu_natCast_inj ha).1 this)

theorem minP : MinP k := PositivityTheory.Exh.minP

end CompanionTheory.Exh

end

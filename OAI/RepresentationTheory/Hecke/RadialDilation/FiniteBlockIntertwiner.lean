module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockChart
public import OAI.RepresentationTheory.Hecke.RadialDilation.PadicTensorCommutant
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockHeisenberg


set_option backward.privateInPublic true
@[expose] public section

/-! # Finite Block Intertwiner -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization

noncomputable section

/-! Projected local phase actions give actual finite Weil intertwining identities. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]
variable {Place : Type*} [Fintype Place] [DecidableEq Place] (μ : Place)
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : Theta.PoissonAutomorphyNormalizationData.WeilData (Place × Fin 3) MpR MpF MpA)

def finiteBlockPhase (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) : Sum (Place × Fin 3) (Place × Fin 3) → Theta.PoissonAutomorphyNormalizationData.AQf :=
  Sum.elim (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i)))

def finiteBlockHeisenberg (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) :
    Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) →ₗ[ℂ] Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3) :=
  FiniteSchur.Realization.finiteHeisenbergOperator D (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i)))

theorem finiteBlockHeisenberg_transport (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    finiteBlockHeisenberg q μ D v (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ) f) =
      FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
        (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
          (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) f) := by
  have hv : Sum.elim (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i)) = v := by
    funext i
    cases i <;> rfl
  simpa only [finiteBlockHeisenberg, hv] using FiniteBlockHeisenberg.Realization.finiteBlock_heisenberg_operator q μ D
    (fun i => v (Sum.inr i)) (fun i => v (Sum.inl i)) f

theorem finiteWeil_block_intertwines (m : MpF) (φ : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3 → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (hproject : ∀ v, (D.finite.project m).val *ᵥ finiteBlockPhase q μ v = finiteBlockPhase q μ (φ v))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (Place × Fin 3)) :
    D.finite.action m (finiteBlockHeisenberg q μ D v f) =
      finiteBlockHeisenberg q μ D (φ v) (D.finite.action m f) := by
  apply Subtype.ext
  funext x
  have h := D.finite.intertwines m
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inr i)))
    (FiniteBlockChart.Realization.finiteBlockInclusion q μ (fun i => v (Sum.inl i))) f (finiteBlockHeisenberg q μ D v f)
    (fun _ => rfl) x
  change (D.finite.action m (finiteBlockHeisenberg q μ D v f)).val x =
    Theta.PoissonAutomorphyNormalizationData.heisenberg D.finiteCharacter
      (fun i => ((D.finite.project m).val *ᵥ finiteBlockPhase q μ v) (Sum.inl i))
      (fun i => ((D.finite.project m).val *ᵥ finiteBlockPhase q μ v) (Sum.inr i))
      (D.finite.action m f).val x at h
  rw [hproject] at h
  exact h

theorem finiteWeil_block_transport (m : MpF) (φ : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3 → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (hproject : ∀ v, (D.finite.project m).val *ᵥ finiteBlockPhase q μ v = finiteBlockPhase q μ (φ v))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) :
    TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)).symm (D.finite.action m)
      (TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
        (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) v) f) =
    TensorCommutant.Realization.extendTestLinear (PadicTensorCommutant.Realization.padicTestHeisenberg q (FiniteSchur.Realization.finiteLocalCharacter q D)
      (FiniteSchur.Realization.finiteLocalCharacter_continuous q D) (φ v))
      (TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)).symm (D.finite.action m) f) := by
  let E := FiniteLocalOperators.Realization.finiteProductTestEquiv (FiniteBlockChart.Realization.finiteBlockChart q μ)
  let W := TensorCommutant.Realization.conjugateLinearAut E.symm (D.finite.action m)
  have hEW (a : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × FiniteBlockChart.Realization.FiniteAwayPosition q μ)) : E (W a) = D.finite.action m (E a) :=
    E.apply_symm_apply _
  change W (TensorCommutant.Realization.extendTestLinear _ f) = TensorCommutant.Realization.extendTestLinear _ (W f)
  apply E.injective
  rw [hEW, ← finiteBlockHeisenberg_transport, finiteWeil_block_intertwines q μ D m φ hproject,
    ← finiteBlockHeisenberg_transport, hEW]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteBlockIntertwiner.Realization

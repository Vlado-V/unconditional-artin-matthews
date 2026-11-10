module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.TensorAction
public import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! # Padic Tensor Commutant -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PadicTensorCommutant.Realization

noncomputable section

section

/-! The actual p-adic Heisenberg action isolates the auxiliary tensor factor. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]

def padicTestHeisenberg (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) :=
  (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3).symm.toLinearMap.comp
    ((Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v).toLinearMap.comp
      (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3).toLinearMap)

theorem padicTestHeisenberg_realization (ψ : AddChar ℚ_[q] ℂ)
    (hψ : Continuous (fun x : ℚ_[q] => ψ x)) (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3)
    (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) :
    FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3 (padicTestHeisenberg q ψ hψ v f) =
      Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3 f) := by
  exact (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3).apply_symm_apply _

theorem padic_test_commutant_scalar (ψ : AddChar ℚ_[q] ℂ)
    (hψ : Continuous (fun x : ℚ_[q] => ψ x)) (hnontrivial : ∃ t, ψ t ≠ 1)
    (hunit : ∀ t, ‖ψ t‖ = 1)
    (A : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (Mem.Realization.Position q))
    (hA : ∀ v f, A (padicTestHeisenberg q ψ hψ v f) = padicTestHeisenberg q ψ hψ v (A f)) :
    ∃ c : ℂ, ∀ f, A f = c • f := by
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3
  let B : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 →ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 :=
    L.toLinearMap.comp (A.comp L.symm.toLinearMap)
  have hB (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) : B (L f) = L (A f) := by simp [B]
  have hcomm v f : B (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v f) =
      Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v (B f) := by
    obtain ⟨f, rfl⟩ := L.surjective f
    calc
      _ = B (L (padicTestHeisenberg q ψ hψ v f)) :=
        congrArg B (padicTestHeisenberg_realization q ψ hψ v f).symm
      _ = L (A (padicTestHeisenberg q ψ hψ v f)) := hB _
      _ = L (padicTestHeisenberg q ψ hψ v (A f)) := congrArg L (hA v f)
      _ = Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v (L (A f)) :=
        padicTestHeisenberg_realization q ψ hψ v (A f)
      _ = _ := congrArg (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v) (hB f).symm
  obtain ⟨c, hc⟩ := Weil.UnitarySplitting.UltraMultiplier.Construction.ultra_commutant_scalar
    (LocalLiftChoice.Realization.padic_not_discrete q) ψ hψ hnontrivial hunit B hcomm
  refine ⟨c, ?_⟩
  intro f
  apply L.injective
  rw [map_smul]
  exact (hB f).symm.trans (hc (L f))

def padicVacuumTest : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) :=
  TensorAction.Realization.radialTest q ⟨Mem.Realization.radialBall q 0, Mem.Realization.radialBall_mem q 0⟩

theorem padicVacuumTest_zero : (padicVacuumTest q).val 0 = 1 := by
  simp [padicVacuumTest, TensorAction.Realization.radialTest, Mem.Realization.radialBall]

/-- No abstract irreducibility hypothesis remains in the p-adic factorization. -/
theorem padic_tensor_commutant_factors
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (ψ : AddChar ℚ_[q] ℂ) (hψ : Continuous (fun x : ℚ_[q] => ψ x))
    (hnontrivial : ∃ t, ψ t ≠ 1) (hunit : ∀ t, ‖ψ t‖ = 1)
    (U : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × Y) →ₗ[ℂ] TestSections.Realization.lcCompactSpace (Mem.Realization.Position q × Y))
    (hU : ∀ v f, U (TensorCommutant.Realization.extendTestLinear (padicTestHeisenberg q ψ hψ v) f) =
      TensorCommutant.Realization.extendTestLinear (padicTestHeisenberg q ψ hψ v) (U f)) :
    U = TensorCommutant.Realization.rightTestLinear (TensorCommutant.Realization.auxiliaryTraceOperator U (padicVacuumTest q) 0) :=
  TensorCommutant.Realization.local_commutant_factors (padicTestHeisenberg q ψ hψ)
    (padic_test_commutant_scalar q ψ hψ hnontrivial hunit) U hU
    (padicVacuumTest q) 0 (padicVacuumTest_zero q)

end

/-! The actual local Weil action intertwines the actual p-adic test-space Heisenberg operators. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]
local instance c410PadicWeilIntertwiner_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410PadicWeilIntertwiner_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

def padicTestWeil (ψ : AddChar ℚ_[q] ℂ) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ) :
    TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) ≃ₗ[ℂ] TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) :=
  TensorCommutant.Realization.conjugateLinearAut (FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3).symm (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g)

theorem weil_ultraHeisenberg_covariance (ψ : AddChar ℚ_[q] ℂ)
    (hψ : Continuous (fun x : ℚ_[q] => ψ x)) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3) :
    Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v f) =
      Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ g) v) (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g f) := by
  apply Subtype.ext
  exact (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation_intertwines ℚ_[q] 3 ψ g v f
    (Weil.UnitarySplitting.UltraMultiplier.Construction.ultraHeisenbergOperator ψ hψ v f)).mp rfl

theorem padicTestWeil_intertwines (ψ : AddChar ℚ_[q] ℂ)
    (hψ : Continuous (fun x : ℚ_[q] => ψ x)) (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ)
    (v : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℚ_[q] 3) (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) :
    padicTestWeil q ψ g (padicTestHeisenberg q ψ hψ v f) =
      padicTestHeisenberg q ψ hψ (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ g) v)
        (padicTestWeil q ψ g f) := by
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3
  have hL (f : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q)) : L (padicTestWeil q ψ g f) =
      Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g (L f) := L.apply_symm_apply _
  apply L.injective
  rw [hL, padicTestHeisenberg_realization, padicTestHeisenberg_realization, hL]
  exact weil_ultraHeisenberg_covariance q ψ hψ g v (L f)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PadicTensorCommutant.Realization

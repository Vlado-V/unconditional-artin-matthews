module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteLocalOperators
public import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteTestEmbedding
public import OAI.RepresentationTheory.Hecke.RadialDilation.LocalLiftChoice
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Tensor Action -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization

noncomputable section

/-! The constructed tensor action has the required radial substitution law. -/

open scoped Classical

variable (q : ℕ) [Fact q.Prime]
variable {ι X : Type*} [Fintype ι] [TopologicalSpace X] [T2Space X]

def radialTest (b : Cm.radialInput q) : TestSections.Realization.lcCompactSpace (Mem.Realization.Position q) := ⟨b.val, FiniteTestEmbedding.Realization.radial_regular q b⟩

theorem radialTest_local (b : Cm.radialInput q) :
    FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3 (radialTest q b) = Mem.Realization.radialSchwartzEmbedding q b := rfl

theorem finiteRadialEmbedding_tensor (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (φ : X → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ) (b : Cm.radialInput q) :
    FiniteTestEmbedding.Realization.finiteRadialEmbedding q e φ hφ hcφ b =
      FiniteLocalOperators.Realization.finiteProductTestEquiv e (TensorCommutant.Realization.tensorTest (radialTest q b) ⟨φ, hφ, hcφ⟩) := by
  apply Subtype.ext
  funext x
  change b.val (e x).1 * φ (e x).2 =
    (TensorCommutant.Realization.tensorTest (radialTest q b) ⟨φ, hφ, hcφ⟩).val ((e x).1, (e x).2)
  rw [TensorCommutant.Realization.tensorTest_apply]
  rfl

theorem tensorTest_smul_left {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Y] [T2Space Z] (c : ℂ) (f : TestSections.Realization.lcCompactSpace Y) (g : TestSections.Realization.lcCompactSpace Z) :
    TensorCommutant.Realization.tensorTest (c • f) g = c • TensorCommutant.Realization.tensorTest f g := by
  apply Subtype.ext
  funext p
  change g.val p.2 * (c * f.val p.1) = c * (g.val p.2 * f.val p.1)
  ring

theorem finiteLocalOperatorHom_radial (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (φ : X → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (U : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3 ≃ₗ[ℂ] Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℚ_[q] 3)
    (A : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q) (ξ : ℂ)
    (hU : ∀ b, U (Mem.Realization.radialSchwartzEmbedding q b) = ξ • Mem.Realization.radialSchwartzEmbedding q (A b))
    (b : Cm.radialInput q) :
    FiniteLocalOperators.Realization.finiteLocalOperatorHom q e U (FiniteTestEmbedding.Realization.finiteRadialEmbedding q e φ hφ hcφ b) =
      ξ • FiniteTestEmbedding.Realization.finiteRadialEmbedding q e φ hφ hcφ (A b) := by
  let L := FiniteLocalOperators.Realization.nonarchTestSpaceEquiv ℚ_[q] 3
  have hl : L.symm (U (L (radialTest q b))) = ξ • radialTest q (A b) := by
    apply L.injective
    rw [L.apply_symm_apply, map_smul]
    exact hU b
  rw [finiteRadialEmbedding_tensor, FiniteLocalOperators.Realization.finiteLocalOperatorHom_tensor]
  change FiniteLocalOperators.Realization.finiteProductTestEquiv e (TensorCommutant.Realization.tensorTest (L.symm (U (L (radialTest q b)))) ⟨φ, hφ, hcφ⟩) = _
  rw [hl, tensorTest_smul_left, map_smul, ← finiteRadialEmbedding_tensor]

local instance c410RadialTensorAction_localInst1 : MeasurableSpace ℚ_[q] := borel ℚ_[q]
local instance c410RadialTensorAction_localInst2 : BorelSpace ℚ_[q] := ⟨rfl⟩

/-- The constructed local action on finite adeles realizes hUq and the
eighth-root phase on the actual embedded radial test functions. -/
theorem actual_radial_tensor_substitution
    (hLocalWeil : Prerequisites.Core.LocalWeil.Proposition)
    (e : (ι → Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ Mem.Realization.Position q × X)
    (φ : X → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (ψ : AddChar ℚ_[q] ℂ)
    (hContinuous : Continuous (fun t : ℚ_[q] => ψ t))
    (hUnitary : ∀ t : ℚ_[q], ‖ψ t‖ = 1)
    (hNontrivial : ∃ t : ℚ_[q], ψ t ≠ 1)
    (a : ℚ_[q]ˣ) (M : ℕ) (ha : ‖(a : ℚ_[q])‖ = (q : ℝ) ^ (-(M : ℤ)))
    (g : Weil.Local.FunctionsMetaplectic.Construction.Metaplectic ℚ_[q] 3 ψ)
    (hg : Weil.Local.FunctionsMetaplectic.Construction.metaplecticProjection ℚ_[q] 3 ψ g = Weil.Local.Generators.Construction.leviSymplectic (LocalLiftChoice.Realization.scalarGL q a)) :
    ∃ ξ : ℂ, ξ ^ 8 = 1 ∧ ∀ b : Cm.radialInput q,
      FiniteLocalOperators.Realization.finiteLocalOperatorHom q e (Weil.Local.FunctionsMetaplectic.Construction.weilRepresentation ℚ_[q] 3 ψ g)
          (FiniteTestEmbedding.Realization.finiteRadialEmbedding q e φ hφ hcφ b) =
        ξ • FiniteTestEmbedding.Realization.finiteRadialEmbedding q e φ hφ hcφ
          (Mem.Realization.normalizedScalarSubstitution q (a : ℚ_[q]) M ha b) := by
  obtain ⟨ξ, hξ, hU⟩ := LocalLiftChoice.Realization.every_local_lift_radial_substitution q hLocalWeil ψ
    hContinuous hUnitary hNontrivial a M ha g hg
  refine ⟨ξ, hξ, ?_⟩
  exact finiteLocalOperatorHom_radial q e φ hφ hcφ _ _ ξ hU

end

end OAI.RepresentationTheory.Hecke.RadialDilation.TensorAction.Realization

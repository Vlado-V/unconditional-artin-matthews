module

public import ArtinMatthews.SourceKPTranslateGramL2
public import ArtinMatthews.SourceKPTranslateCoreGram
public import ArtinMatthews.SourceKPCompactCoreMass
public import ArtinMatthews.SourceKPCompactCoreDensity
public import ArtinMatthews.SourceKPTranslateTraceIntegral
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
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

/-! The Haar adjoint of a translate pullback agrees with the actual core trace. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "YJ" => SourceKPTranslateAutomorphicCompactLevel K hζ T
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "m" => sourceKPCompactCoreMass K hζ 2
local notation "LY" => Lp ℂ 2 μY
local notation "LJ" => Lp ℂ 2 μJ
local notation "π[" t ", " ht "]" => sourceKPTranslateAutomorphicCompactMap K hζ T t ht
local notation "P[" t ", " ht "]" => sourceKPTranslateCompactPullbackL2 K hζ T t ht

private theorem scalarCore_pullback_ae (t : Gf) (ht : J ≤ D t) (f : C2) :
    (P[t, ht] (m f) : YJ → ℂ) =ᵐ[μJ] f.val ∘ π[t, ht] :=
  (sourceKPTranslateCompactPullbackL2_coe K hζ T t ht (m f)).trans
    ((sourceKPTranslateAutomorphicCompactMap_quasiMeasurePreserving K hζ T t ht).ae_eq_comp
      (sourceKPCompactCoreMass_coe K hζ f))

private theorem coreGram_inner (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : C2) :
    inner ℂ (P[t, ht] (m f)) (P[u, hu] (m g)) =
      inner ℂ (m f) (m (sourceKPTranslateCoreGram K hζ T t ht u hu g)) := by
  let G := sourceKPTranslateCoreGram K hζ T t ht u hu g
  let v : YJ → ℂ := fun x => inner ℂ (f.val (π[t, ht] x)) (g.val (π[u, hu] x))
  have hv : Continuous v :=
    (f.prop.1.comp (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T t ht)).inner
      (g.prop.1.comp (sourceKPTranslateAutomorphicCompactMap_continuous K hζ T u hu))
  have he : (fun x : YJ => inner ℂ (P[t, ht] (m f) x) (P[u, hu] (m g) x)) =ᵐ[μJ] v := by
    filter_upwards [scalarCore_pullback_ae K hζ T t ht f,
      scalarCore_pullback_ae K hζ T u hu g] with x hx hy
    exact congrArg₂ (inner ℂ) hx hy
  have hint : Integrable v μJ :=
    (L2.integrable_inner (P[t, ht] (m f)) (P[u, hu] (m g))).congr he
  have htrace (y : Y) : sourceKPTranslateCompactTrace K hζ T t ht v y =
      inner ℂ (f.val y) (G.val y) := by
    obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    rw [sourceKPTranslateCompactTrace_upper, sourceKPTranslateCoreGram_upper K hζ T t ht u hu g,
      inner_sum]
    apply Finset.sum_congr rfl
    intro c _
    simp only [v, sourceKPTranslateAutomorphicCompactMap_upperMk]
    exact congrArg (fun d => inner ℂ (f.val (sourceKPUpperToCompact K hζ d p)) _) c.prop
  calc
    _ = ∫ x, v x ∂μJ := (L2.inner_def _ _).trans (integral_congr_ae he)
    _ = ∫ y, sourceKPTranslateCompactTrace K hζ T t ht v y ∂μY :=
      (sourceKPTranslateCompactTrace_integral K hζ T t ht v hv hint).symm
    _ = inner ℂ (m f) (m G) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [sourceKPCompactCoreMass_coe K hζ f, sourceKPCompactCoreMass_coe K hζ G]
        with y hf hg
      exact (htrace y).trans (congrArg₂ (inner ℂ) hf.symm hg.symm)

theorem sourceKPTranslateScalarGramL2_coreMass (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (g : C2) :
    sourceKPTranslateScalarGramL2 K hζ T t ht u hu (m g) =
      m (sourceKPTranslateCoreGram K hζ T t ht u hu g) := by
  let A := sourceKPTranslateScalarGramL2 K hζ T t ht u hu
  let G := sourceKPTranslateCoreGram K hζ T t ht u hu g
  apply ext_inner_left ℂ
  intro f
  refine (sourceKPCompactCoreMass_denseRange K hζ).induction_on
    (p := fun a : LY => inner ℂ a (A (m g)) = inner ℂ a (m G)) f
    (isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)) ?_
  intro f
  exact (sourceKPTranslateScalarGramL2_inner K hζ T t ht u hu (m f) (m g)).symm.trans
    (coreGram_inner K hζ T t ht u hu f g)

end
end ArtinMatthews

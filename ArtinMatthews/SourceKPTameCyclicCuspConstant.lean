module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPTameJacquetCuspConstant
public import ArtinMatthews.SourceKPTameSphericalTranslateForm
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
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! Exterior coset constancy for the entire actual cyclic span. The
spherical translate form reduces each generator to the exact
signed Bruhat shell formula, and the property is linear. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical Filter
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "f₀" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "I₀" => sourceKPTameExteriorInducedSpace K hζ S₀ P
local notation "B" => sourceLocalBall K P.val

def sourceKPTameCuspConstantSpace : Submodule ℂ I₀ where
  carrier := {f | ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ x t : L, x ∉ B (R : ℤ) → t ∈ B (R : ℤ) →
    f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))) = f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))}
  zero_mem' := ⟨0, fun _ _ _ _ _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨R₀, hf⟩ ⟨R₁, hg⟩
    refine ⟨max R₀ R₁, fun R hR x t hx ht => ?_⟩
    change f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))) +
      g.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))) =
      f.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) + g.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))
    rw [hf R ((le_max_left R₀ R₁).trans hR) x t hx ht,
      hg R ((le_max_right R₀ R₁).trans hR) x t hx ht]
  smul_mem' := by
    rintro c f ⟨R₀, hf⟩
    exact ⟨R₀, fun R hR x t hx ht => congrArg (c • ·) (hf R hR x t hx ht)⟩

theorem sourceKPTameSphericalCyclicSpace_le_cuspConstant :
    sourceKPTameSphericalCyclicSpace K hζ S₀ P ≤ sourceKPTameCuspConstantSpace K hζ S₀ P := by
  apply Submodule.span_le.mpr
  rintro f ⟨g, rfl⟩
  obtain ⟨c, u, e, hg⟩ := sourceKPTameSphericalTranslate_normal_form K hζ S₀ P g
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (sourceJacquetBall_eventually_contains K P.val u)
  refine ⟨max R₀ (-e).toNat, fun R hR x t hx ht => ?_⟩
  have hu : u ∈ B (R : ℤ) := hR₀ R ((le_max_left R₀ (-e).toNat).trans hR)
  have he : -e ≤ (R : ℤ) := by
    have h := (le_max_right R₀ (-e).toNat).trans hR
    omega
  have hxu : x + u ∉ B (R : ℤ) := fun h => hx ((sourceJacquetBall_translate_mem_iff K P.val _ u x hu).mp h)
  have hEval (z : L) : (ρ₀ g f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper z)) =
      c • sourceKPTameJacquetPoint K hζ S₀ P e (z + u) := by
    rw [hg]
    change c • Subtype.val f₀ (((l₀ sourceGL2Weyl * l₀ (sourceGL2Upper z)) * l₀ (sourceGL2Upper u)) *
      l₀ (sourceGL2Diagonal (π₀ ^ e))) = _
    rw [mul_assoc (l₀ sourceGL2Weyl), sourceFiniteKP2ProjectiveLift_upper_add]
    rfl
  change (ρ₀ g f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))) =
    (ρ₀ g f₀).val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))
  rw [hEval, hEval, show x + t + u = x + u + t by abel,
    sourceKPTameJacquetPoint_add_of_outside K hζ S₀ P e R he (x + u) t (lt_of_not_ge hxu) ht]

theorem sourceKPTameCyclic_cusp_eventually_constant (f : sourceKPTameSphericalCyclicSpace K hζ S₀ P) :
    ∃ R₀ : ℕ, ∀ R ≥ R₀, ∀ x t : L, x ∉ B (R : ℤ) → t ∈ B (R : ℤ) →
      f.val.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (x + t))) =
        f.val.val (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) :=
  sourceKPTameSphericalCyclicSpace_le_cuspConstant K hζ S₀ P f.property

end
end ArtinMatthews

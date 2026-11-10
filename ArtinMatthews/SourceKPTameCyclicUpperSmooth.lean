module

public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKPTameJacquetSignedDiagonal
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

/-! Actual small-upper-ball invariance on the algebraic cyclic
representation. This is the exact invariance needed for finite
Jacquet averaging. It follows from the genuine root and torus lifts. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "f₀" => sourceKPTameExteriorSphericalSection K hζ S₀ P
local notation "ρ₀" => sourceKPTameExteriorInducedRepresentation K hζ S₀ P
local notation "I₀" => sourceKPTameExteriorInducedSpace K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val

theorem sourceKPTameExterior_diagonal_translate_upper_fixed (e : ℤ) (t : L) (ht : ν₀ t ≤ WithZero.exp (-e)) :
    ρ₀ (l₀ (sourceGL2Upper t)) (ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀) =
      ρ₀ (l₀ (sourceGL2Diagonal (π₀ ^ e))) f₀ := by
  let y := π₀ ^ e
  have hy : ν₀ (y : L) = WithZero.exp (-e) := by
    dsimp only [y]
    rw [Units.val_zpow_eq_zpow_val, sourceJacquetFrequency_valuation K P.val _ hπ₀]
  have hsmall : ν₀ (t / (y : L)) ≤ 1 := by
    rw [map_div₀, hy]
    exact (div_le_one₀ (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mpr ht
  have hfix := sourceKPTameExteriorSpherical_upper_integral_right K hζ S₀ P (t / (y : L)) hsmall
  change ρ₀ (l₀ (sourceGL2Upper t)) (ρ₀ (l₀ (sourceGL2Diagonal y)) f₀) = _
  rw [← Module.End.mul_apply, ← map_mul, sourceFiniteKP2ProjectiveLift_upper_diagonal,
    map_mul, Module.End.mul_apply, hfix]

def sourceKPTameUpperSmallInvariant : Submodule ℂ I₀ where
  carrier := {f | ∃ M : ℕ, ∀ t : L, ν₀ t ≤ WithZero.exp (-(M : ℤ)) → ρ₀ (l₀ (sourceGL2Upper t)) f = f}
  zero_mem' := ⟨0, fun t _ => map_zero (ρ₀ (l₀ (sourceGL2Upper t)))⟩
  add_mem' := by
    rintro f g ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨max M N, fun t ht => ?_⟩
    have h₁ : ν₀ t ≤ WithZero.exp (-(M : ℤ)) :=
      ht.trans (WithZero.exp_le_exp.mpr (by have h := le_max_left M N; omega))
    have h₂ : ν₀ t ≤ WithZero.exp (-(N : ℤ)) :=
      ht.trans (WithZero.exp_le_exp.mpr (by have h := le_max_right M N; omega))
    rw [map_add, hM t h₁, hN t h₂]
  smul_mem' := by
    rintro c f ⟨M, hM⟩
    refine ⟨M, fun t ht => ?_⟩
    rw [map_smul, hM t ht]

theorem sourceKPTameSphericalCyclicSpace_le_upperSmallInvariant :
    sourceKPTameSphericalCyclicSpace K hζ S₀ P ≤ sourceKPTameUpperSmallInvariant K hζ S₀ P := by
  apply Submodule.span_le.mpr
  rintro f ⟨g, rfl⟩
  obtain ⟨c, x, e, hg⟩ := sourceKPTameSphericalTranslate_normal_form K hζ S₀ P g
  refine ⟨e.toNat, fun t ht => ?_⟩
  have ht' : ν₀ t ≤ WithZero.exp (-e) := ht.trans (WithZero.exp_le_exp.mpr (by omega))
  have hcomm : l₀ (sourceGL2Upper t) * l₀ (sourceGL2Upper x) =
      l₀ (sourceGL2Upper x) * l₀ (sourceGL2Upper t) := by
    rw [sourceFiniteKP2ProjectiveLift_upper_add, sourceFiniteKP2ProjectiveLift_upper_add, add_comm t x]
  change ρ₀ (l₀ (sourceGL2Upper t)) (ρ₀ g f₀) = ρ₀ g f₀
  rw [hg, map_smul, ← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply,
    sourceKPTameExterior_diagonal_translate_upper_fixed K hζ S₀ P e t ht']

theorem sourceKPTameCyclic_upper_small_fixed (f : sourceKPTameSphericalCyclicSpace K hζ S₀ P) :
    ∃ M : ℕ, ∀ t : L, ν₀ t ≤ WithZero.exp (-(M : ℤ)) →
      sourceKPTameSphericalCyclicRepresentation K hζ S₀ P (l₀ (sourceGL2Upper t)) f = f := by
  obtain ⟨M, hM⟩ := sourceKPTameSphericalCyclicSpace_le_upperSmallInvariant K hζ S₀ P f.property
  exact ⟨M, fun t ht => Subtype.ext (hM t ht)⟩

end
end ArtinMatthews

module

public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceKPTameIntertwiningShell
public import ArtinMatthews.SourceKPCommRingDiagonal
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKPTameIntertwiningIntegral
public import ArtinMatthews.SourceKPTameJacquetShellPoint
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open SourcePhysical QuadraticWeil VaryingKummerAnalytic AllowedGenerators
open scoped NumberField MatrixGroups SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "k₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "f₀" => Subtype.val (sourceKPTameExteriorSphericalSection K hζ S₀ P)
local notation "fₛ[" s "]" => Subtype.val (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s)
local notation "ρₛ" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℝ)

theorem sourceKPTameParametricSpherical_base (g : SourceFiniteKP2Projective K hζ P.val) :
    fₛ[-1/6] g = f₀ g := by
  obtain ⟨b, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa_range K hζ P.val h₆ g
  rw [sourceKPTameParametricSphericalSection_factor K hζ P.val h₆ π₀ hπ₀ (-1/6) g b k hg]
  have ht : sourceKPTameBorelTwist K hζ P.val (-1/6) b = 1 := by
    change Complex.exp (-((-1/6 : ℂ)+1/6) *
      (sourceKPValuationOrder ν₀ (sourceFiniteKPNormalizedBorelBase K hζ P.val
        ((sourceFiniteKPProjectiveBorelEquiv K hζ P.val).symm b)) : ℂ) *
      (Real.log Q₀ : ℂ)) = 1
    norm_num
  rw [ht, one_smul]

theorem sourceKPTameParametricSpherical_covariant (s : ℂ)
    (b : SourceFiniteKPProjectiveBorel K hζ P.val) (g : SourceFiniteKP2Projective K hζ P.val) :
    fₛ[s] (b.val*g) = ρₛ s b (fₛ[s] g) :=
  (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).property b g

theorem sourceKPTameParametricSpherical_compact (s : ℂ) (k : SourceFiniteKP2Integral K P.val) :
    fₛ[s] (k₀ k) = sourceJacquetBasis 0 := by
  let c : SourceFiniteKP2ProjectiveCompact K hζ P.val h₆ := ⟨k₀ k, ⟨k, rfl⟩⟩
  unfold sourceKPTameParametricSphericalSection
  rw [sourceAlgebraicSphericalSection_factor _ _ _ _ _ _
    (b := 1) (c := c) (one_mul (k₀ k)).symm, map_one]
  rfl

theorem sourceKPTameParametricBorel_upper (s : ℂ) (x : L) (v : ZMod 3 → ℂ) :
    ρₛ s (sourceFiniteKPProjectiveBorelUpper K hζ P.val x) v = v := by
  have ht : sourceKPTameBorelTwist K hζ P.val s
      (sourceFiniteKPProjectiveBorelUpper K hζ P.val x) = 1 := by
    rw [sourceFiniteKPProjectiveBorelUpper, sourceKPTameBorelTwist_normalized]
    change Complex.exp (-(s+1/6) * (sourceKPValuationOrder ν₀
      (GeneralLinearGroup.det (sourceGL2Upper x)) : ℂ) * (Real.log Q₀ : ℂ)) = 1
    rw [sourceGL2Upper_det, sourceKPValuationOrder_one]
    simp
  change sourceKPTameBorelTwist K hζ P.val s _ •
    sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀ _ v = v
  rw [ht, one_smul, sourceKPTameBorelRepresentation_upper]

theorem sourceKPTameParametricSpherical_weyl_upper_integral (s : ℂ) (x : L) (hx : ν₀ x ≤ 1) :
    fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) = sourceJacquetBasis 0 := by
  let w : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Weyl, sourceKPIntegralMatrix_weyl ν₀⟩
  let n : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Upper x, sourceKPIntegralMatrix_upper ν₀ x hx⟩
  have hw : k₀ w = l₀ sourceGL2Weyl := congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
    (sourceFiniteKP2CompactSection_weyl K hζ P.val h₆)
  have hn : k₀ n = l₀ (sourceGL2Upper x) := congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
    (sourceFiniteKP2CompactSection_upper K hζ P.val h₆ x hx)
  rw [← hw, ← hn, ← map_mul]
  exact sourceKPTameParametricSpherical_compact K hζ S₀ P s (w*n)

theorem sourceKPTameParametricSpherical_weyl_upper_bruhat (s : ℂ) (H : Lˣ)
    (hH : ν₀ ((H : L)⁻¹) ≤ 1) :
    fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper (H : L))) =
      ρₛ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (sourceBruhatDiagonal H))
        (sourceJacquetBasis 0) := by
  let x := (H : L)⁻¹
  let n : SourceFiniteKP2Integral K P.val := ⟨sourceGL2Lower x, sourceKPIntegralMatrix_lower ν₀ x hH⟩
  have hn : k₀ n = l₀ (sourceGL2Lower x) :=
    sourceFiniteKP2ProjectiveCompactSection_lower K hζ P.val h₆ x hH
  rw [sourceFiniteKP2ProjectiveLift_weyl_upper, mul_assoc,
    ← sourceFiniteKPProjectiveBorelUpper_val]
  rw [sourceKPTameParametricSpherical_covariant K hζ S₀ P,
    sourceKPTameParametricBorel_upper K hζ S₀ P]
  rw [← sourceFiniteKPProjectiveBorelDiagonal_val,
    sourceKPTameParametricSpherical_covariant K hζ S₀ P,
    ← hn, sourceKPTameParametricSpherical_compact K hζ S₀ P]

theorem sourceKPTameParametricSpherical_open_shell (s : ℂ) (l : ℕ) (u : Lˣ)
    (hu : ν₀ (u : L) = 1) :
    let x := (π₀ : L)^(-(l : ℤ)) * (u : L)
    fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) =
      sourceKPTameIntertwiningIntegrand K hζ S₀ P s x := by
  let H := π₀^(-(l : ℤ)) * u
  let v := sourceMinusOneUnit L * u^(-2 : ℤ)
  have hx : (H : L) = (π₀ : L)^(-(l : ℤ)) * (u : L) := by
    simp only [H, Units.val_mul, Units.val_zpow_eq_zpow_val]
  have hν : ν₀ (H : L) = WithZero.exp (l : ℤ) := by
    rw [sourceKPValuationOrder_spec ν₀ H,
      sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ u hu, neg_neg]
  have hH : ν₀ ((H : L)⁻¹) ≤ 1 := by
    rw [map_inv₀, hν]
    exact inv_le_one_of_one_le₀ (WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg l))
  have hv : ν₀ (v : L) = 1 := by
    dsimp only [v]
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hu, _root_.one_zpow]
    simp [sourceMinusOneUnit]
  have hd : sourceBruhatDiagonal H = π₀^(2*(l : ℤ)) * v :=
    sourceBruhatDiagonal_uniformizer π₀ u l
  have hweight : sourceKPTameBorelTwist K hζ P.val s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val (sourceBruhatDiagonal H)) =
      sourceKPTameIntertwiningWeight K S₀ P s (H : L) := by
    rw [sourceKPTameBorelTwist_diagonal, hd,
      sourceKPValuationOrder_uniformizer_unit K P.val π₀ hπ₀ _ v hv,
      sourceKPTameIntertwiningWeight_shell K S₀ P s l (H : L)
        ((sourceJacquetValuationShell_mem K P.val (l : ℤ) (H : L)).mpr hν)]
    push_cast
    congr 1
    ring
  dsimp only
  rw [← hx, sourceKPTameParametricSpherical_weyl_upper_bruhat K hζ S₀ P s H hH]
  change sourceKPTameBorelTwist K hζ P.val s _ •
    sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀ _ (sourceJacquetBasis 0) = _
  rw [hweight, ← sourceKPTameExteriorSpherical_weyl_upper_bruhat K hζ S₀ P H hH]
  have hdiag : sourceGL2Diagonal (1 : Lˣ) = 1 := by
    rw [← sourceKPDiagonalHom_field]
    exact map_one _
  simp only [sourceKPTameIntertwiningIntegrand, sourceKPTameJacquetPoint, zpow_zero,
    hdiag, sourceFiniteKP2ProjectiveLift_one, mul_one]

/-- The integrand is the value of the actual parameter-dependent induced
spherical section on the open Bruhat cell. -/
theorem sourceKPTameParametricSpherical_open (s : ℂ) (x : L) :
    fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) =
      sourceKPTameIntertwiningIntegrand K hζ S₀ P s x := by
  by_cases hx : ν₀ x ≤ 1
  · have hb : x ∈ sourceLocalBall K P.val 0 := by
      change ν₀ x ≤ WithZero.exp (0 : ℤ)
      rwa [WithZero.exp_zero]
    rw [sourceKPTameParametricSpherical_weyl_upper_integral K hζ S₀ P s x hx,
      sourceKPTameIntertwiningIntegrand_on_zero K hζ S₀ P s x hb]
  · have hgt : 1 < ν₀ x := lt_of_not_ge hx
    have hv0 : ν₀ x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hgt)
    let k := WithZero.log (ν₀ x)
    have hv : ν₀ x = WithZero.exp k := (WithZero.exp_log hv0).symm
    have hk : 0 < k := by
      rw [hv] at hgt
      exact WithZero.one_lt_exp_iff.mp hgt
    let n := k.toNat
    have hn : (n : ℤ) = k := Int.toNat_of_nonneg hk.le
    let a := (π₀ : L)^(n : ℤ) * x
    have ha : ν₀ a = 1 := by
      dsimp only [a]
      rw [map_mul, sourceJacquetFrequency_valuation K P.val _ hπ₀, hn, hv,
        ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact zero_ne_one ha
    let u := Units.mk0 a ha0
    have hrecover : (π₀ : L)^(-(n : ℤ)) * (u : L) = x := by
      change (π₀ : L)^(-(n : ℤ)) * ((π₀ : L)^(n : ℤ) * x) = x
      rw [← mul_assoc, ← zpow_add₀ (Units.ne_zero π₀), neg_add_cancel, zpow_zero, one_mul]
    have h := sourceKPTameParametricSpherical_open_shell K hζ S₀ P s n u ha
    simpa only [hrecover] using h

end
end ArtinMatthews

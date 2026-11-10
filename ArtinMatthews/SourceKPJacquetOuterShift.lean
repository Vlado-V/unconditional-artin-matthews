module

public import ArtinMatthews.SourceAlgebraicInduction
public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.SourceJacquetAdditiveTranslation
public import ArtinMatthews.SourceKPJacquetTinyUnits
public import ArtinMatthews.SourceKPLocalBorelRelations
public import ArtinMatthews.SourceKPProjectiveSections
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
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

/-! A fixed additive shift preserves the exterior open-cell value on the
genuine cover once the relative shift is in the Hensel cube neighborhood. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical Filter
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem sourceKPJacquet_bruhat_diagonal_unit_cube (ρ : Representation ℂ B₀ V) (u z : Lˣ)
    (hz : ν₀ ((z ^ 3 : Lˣ) : L) = 1)
    (hcube : ∀ y : Lˣ, ν₀ ((y ^ 3 : Lˣ) : L) = 1 → ∀ v : V, ρ (d₀ (y ^ 3)) v = v)
    (v : V) : ρ (d₀ (sourceBruhatDiagonal (u * z ^ 3))) v = ρ (d₀ (sourceBruhatDiagonal u)) v := by
  let w : Lˣ := (z⁻¹) ^ 2
  have hw : w ^ 3 = ((z ^ 3)⁻¹) ^ 2 := by dsimp only [w]; group
  have hdiag : sourceBruhatDiagonal (u * z ^ 3) = sourceBruhatDiagonal u * w ^ 3 := by
    rw [hw]
    apply Units.ext
    change -(((u * z ^ 3 : Lˣ) : L)⁻¹) ^ 2 =
      -((u : L)⁻¹) ^ 2 * ((((z ^ 3)⁻¹) ^ 2 : Lˣ) : L)
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, mul_inv_rev, mul_pow]
    ring
  have hwv : ν₀ ((w ^ 3 : Lˣ) : L) = 1 := by
    rw [hw, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, map_pow, map_inv₀, hz, inv_one, one_pow]
  have hm : d₀ (sourceBruhatDiagonal u * w ^ 3) = d₀ (sourceBruhatDiagonal u) * d₀ (w ^ 3) := by
    rw [sourceKPLocalBorelDiagonal_mul K hζ P, sourceFiniteKPHilbert_cube_right K hζ P, one_pow]
    have h1 : sourceFiniteKPProjectiveBorelCenter K hζ P 1 = 1 := by
      apply Subtype.ext
      exact map_one _
    rw [h1, one_mul]
  rw [hdiag, hm, map_mul, Module.End.mul_apply, hcube w hwv]

theorem sourceKPJacquet_open_cell_eval_of_lower_fixed (ρ : Representation ℂ B₀ V)
    (f : sourceAlgebraicInducedSpace _ ρ)
    (hu : ∀ x : L, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (u : Lˣ) (hLower : f.val (n₋ ((u : L)⁻¹)) = f.val 1) :
    f.val (w₀ * n₀ (u : L)) = ρ (d₀ (sourceBruhatDiagonal u)) (f.val 1) := by
  rw [sourceFiniteKP2ProjectiveLift_weyl_upper, mul_assoc,
    ← sourceFiniteKPProjectiveBorelUpper_val, f.property, hu,
    ← sourceFiniteKPProjectiveBorelDiagonal_val, f.property, hLower]

theorem sourceKPJacquet_open_cell_eventual_fixed_shift (ρ : Representation ℂ B₀ V)
    (f : sourceAlgebraicInducedSpace _ ρ)
    (hu : ∀ x : L, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hcube : ∀ y : Lˣ, ν₀ ((y ^ 3 : Lˣ) : L) = 1 → ∀ v : V, ρ (d₀ (y ^ 3)) v = v)
    (N : ℕ) (hLower : ∀ t ∈ B (-(N : ℤ)), f.val (n₋ t) = f.val 1) (a : L) :
    ∃ R₀ : ℕ, a ∈ B (R₀ : ℤ) ∧ ∀ y ∉ B (R₀ : ℤ),
      f.val (w₀ * n₀ (y + a)) = f.val (w₀ * n₀ y) := by
  obtain ⟨M, _, hTiny⟩ := sourceKPJacquet_tiny_unit_cube K P
  obtain ⟨Ra, hRa⟩ := eventually_atTop.mp (sourceJacquetBall_eventually_contains K P a)
  let R := Ra + M + N
  have hRaR : Ra ≤ R := by dsimp only [R]; omega
  refine ⟨R, hRa R hRaR, ?_⟩
  intro y hy
  have hY : WithZero.exp (R : ℤ) < ν₀ y := lt_of_not_ge hy
  have hYp : 0 < ν₀ y := (pos_iff_ne_zero.mpr WithZero.exp_ne_zero).trans hY
  have hY0 : y ≠ 0 := (Valuation.ne_zero_iff ν₀).mp hYp.ne'
  have hA : ν₀ a ≤ WithZero.exp (Ra : ℤ) := hRa Ra le_rfl
  have hA_lt : ν₀ a < ν₀ y :=
    (hA.trans (WithZero.exp_le_exp.mpr (by exact_mod_cast hRaR))).trans_lt hY
  have hPlus : ν₀ (y + a) = ν₀ y := (ν₀).map_add_eq_of_lt_left hA_lt
  have hPlus0 : y + a ≠ 0 := (Valuation.ne_zero_iff ν₀).mp (by rw [hPlus]; exact hYp.ne')
  have hInv : y⁻¹ ∈ B (-(N : ℤ)) := by
    change ν₀ y⁻¹ ≤ WithZero.exp (-(N : ℤ))
    rw [map_inv₀, WithZero.exp_neg]
    apply (inv_le_inv₀ hYp (pos_iff_ne_zero.mpr WithZero.exp_ne_zero)).mpr
    exact (WithZero.exp_le_exp.mpr (by dsimp only [R]; omega)).trans hY.le
  have hInvPlus : (y + a)⁻¹ ∈ B (-(N : ℤ)) := by
    change ν₀ (y + a)⁻¹ ≤ WithZero.exp (-(N : ℤ))
    rw [map_inv₀, hPlus, ← map_inv₀]
    exact hInv
  let u := Units.mk0 y hY0
  let u' := Units.mk0 (y + a) hPlus0
  let z := u' / u
  have hz : ((z : L) - 1) ∈ B (-(M : ℤ)) := by
    change ν₀ (((u' / u : Lˣ) : L) - 1) ≤ WithZero.exp (-(M : ℤ))
    rw [Units.val_div_eq_div_val]
    change ν₀ ((y + a) / y - 1) ≤ WithZero.exp (-(M : ℤ))
    rw [show (y + a) / y - 1 = a / y by field_simp [hY0]; ring, map_div₀]
    apply (div_le_iff₀ hYp).mpr
    calc
      _ ≤ WithZero.exp (Ra : ℤ) := hA
      _ ≤ WithZero.exp (-(M : ℤ) + (R : ℤ)) :=
        WithZero.exp_le_exp.mpr (by dsimp only [R]; omega)
      _ = WithZero.exp (-(M : ℤ)) * WithZero.exp (R : ℤ) := WithZero.exp_add _ _
      _ ≤ WithZero.exp (-(M : ℤ)) * ν₀ y := mul_le_mul_of_nonneg_left hY.le zero_le
  obtain ⟨w, hw, hwv⟩ := hTiny z hz
  have he : u' = u * w ^ 3 := by
    calc
      u' = (u' / u) * u := (div_mul_cancel u' u).symm
      _ = u * z := mul_comm _ _
      _ = _ := by rw [hw]
  have hval : ν₀ ((w ^ 3 : Lˣ) : L) = 1 := hw ▸ hwv
  change f.val (w₀ * n₀ (u' : L)) = f.val (w₀ * n₀ (u : L))
  rw [sourceKPJacquet_open_cell_eval_of_lower_fixed K hζ P ρ f hu u' (hLower _ hInvPlus),
    sourceKPJacquet_open_cell_eval_of_lower_fixed K hζ P ρ f hu u (hLower _ hInv), he]
  exact sourceKPJacquet_bruhat_diagonal_unit_cube K hζ P ρ u w hval hcube _

end
end ArtinMatthews

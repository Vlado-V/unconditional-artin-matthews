module

public import ArtinMatthews.SourceKPJacquetDiagonalScale
public import ArtinMatthews.SourceKPJacquetBallCancellation
public import ArtinMatthews.SourceKPJacquetOuterShift
public import ArtinMatthews.StandardLocalBallDilation
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! An explicit stabilization radius for the frequency-twisted integral.
One fixed phase shift on the outer region suffices at every place. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
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
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "n₋" => fun t : L => l₀ (sourceGL2Lower t)
local notation "d₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
local notation "I₀" => sourceAlgebraicInducedSpace B₀ ρ

variable (hUpper : ∀ x : P.adicCompletion K, ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hCube : ∀ y : (P.adicCompletion K)ˣ,
      sourceLocalValuation K P (((y ^ 3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)) = 1 →
      ∀ v : V, ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v)

include hUpper hCube in
theorem sourceKPJacquet_open_cell_fixed_shift_at (f : I₀) (M N R : ℕ) (hNR : N ≤ R)
    (hTiny : ∀ z : Lˣ, ((z : L) - 1) ∈ B (-(M : ℤ)) →
      ∃ w : Lˣ, z = w ^ 3 ∧ ν₀ (z : L) = 1)
    (hLower : ∀ t ∈ B (-(N : ℤ)), f.val (n₋ t) = f.val 1)
    (a : L) (ha : a ∈ B ((R : ℤ) - (M : ℤ))) (y : L) (hy : y ∉ B (R : ℤ)) :
    f.val (w₀ * n₀ (y + a)) = f.val (w₀ * n₀ y) := by
  have hY : WithZero.exp (R : ℤ) < ν₀ y := lt_of_not_ge hy
  have hYp : 0 < ν₀ y := zero_le.trans_lt hY
  have hY0 : y ≠ 0 := (Valuation.ne_zero_iff ν₀).mp hYp.ne'
  have hLogY : (R : ℤ) < WithZero.log (ν₀ y) := by
    apply WithZero.exp_lt_exp.mp
    rw [WithZero.exp_log hYp.ne']
    exact hY
  have hA_lt : ν₀ a < ν₀ y :=
    (show a ∈ B (R : ℤ) from sourceKPJacquetSelfDual_ball_mono K P (by omega) ha).trans_lt hY
  have hPlus : ν₀ (y + a) = ν₀ y := (ν₀).map_add_eq_of_lt_left hA_lt
  have hPlus0 : y + a ≠ 0 := (Valuation.ne_zero_iff ν₀).mp (by rw [hPlus]; exact hYp.ne')
  have hInv : y⁻¹ ∈ B (-(N : ℤ)) := by
    change ν₀ y⁻¹ ≤ WithZero.exp (-(N : ℤ))
    rw [map_inv₀, ← WithZero.exp_log hYp.ne', ← WithZero.exp_neg, WithZero.exp_le_exp]
    omega
  have hInvPlus : (y + a)⁻¹ ∈ B (-(N : ℤ)) := by
    change ν₀ (y + a)⁻¹ ≤ WithZero.exp (-(N : ℤ))
    rw [map_inv₀, hPlus, ← map_inv₀]
    exact hInv
  let u := Units.mk0 y hY0
  let u' := Units.mk0 (y + a) hPlus0
  let z := u' / u
  have hz : ((z : L) - 1) ∈ B (-(M : ℤ)) := by
    change ((u' / u : Lˣ) : L) - 1 ∈ B (-(M : ℤ))
    rw [Units.val_div_eq_div_val]
    change (y + a) / y - 1 ∈ B (-(M : ℤ))
    rw [show (y + a) / y - 1 = a / y by field_simp [hY0]; ring]
    apply (sourceLocalBall_div_mem K P (-(M : ℤ)) u a).mpr
    exact sourceKPJacquetSelfDual_ball_mono K P (by change (R : ℤ) - M ≤ -M + WithZero.log (ν₀ y); omega) ha
  obtain ⟨w, hw, hwv⟩ := hTiny z hz
  have he : u' = u * w ^ 3 := by
    calc
      u' = (u' / u) * u := (div_mul_cancel u' u).symm
      _ = u * z := mul_comm _ _
      _ = _ := by rw [hw]
  have hval : ν₀ ((w ^ 3 : Lˣ) : L) = 1 := hw ▸ hwv
  change f.val (w₀ * n₀ (u' : L)) = f.val (w₀ * n₀ (u : L))
  rw [sourceKPJacquet_open_cell_eval_of_lower_fixed K hζ P ρ f hUpper u' (hLower _ hInvPlus),
    sourceKPJacquet_open_cell_eval_of_lower_fixed K hζ P ρ f hUpper u (hLower _ hInv), he]
  exact sourceKPJacquet_bruhat_diagonal_unit_cube K hζ P ρ u w hval hCube _

def sourceKPJacquetFrequencyRadius (M N : ℕ) (z : Lˣ) : ℕ :=
  ((sourceDifferentExponent K P : ℤ) + 1 - WithZero.log (ν₀ (z : L))).toNat + M + N

variable {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "E" => sourceKPJacquetFrequencyIntegrand K hζ P ρ e
local notation "F" => sourceKPJacquetFrequencyTruncation K hζ P ρ e
local notation "R₀" => sourceKPJacquetFrequencyRadius K P

include hUpper hCube in
theorem sourceKPJacquetFrequencyHasStableValue_cutoff (f : I₀) (M N : ℕ)
    (hTiny : ∀ z : Lˣ, ((z : L) - 1) ∈ B (-(M : ℤ)) →
      ∃ w : Lˣ, z = w ^ 3 ∧ ν₀ (z : L) = 1)
    (hFix : ∀ t ∈ B (-(N : ℤ)), ∀ g : G,
      f.val (g * n₀ t) = f.val g ∧ f.val (g * n₋ t) = f.val g)
    (z : Lˣ) : SourceKPJacquetFrequencyHasStableValue K hζ P ρ e z f (F z (R₀ M N z : ℤ) f) := by
  obtain ⟨b, hb, hψ⟩ := sourceLocalCharacter_next_ball_nontrivial K P
  let a : L := b / (z : L)
  let R := R₀ M N z
  have ha : a ∈ B ((R : ℤ) - (M : ℤ)) := by
    apply (sourceLocalBall_div_mem K P _ z b).mpr
    apply sourceKPJacquetSelfDual_ball_mono K P _ hb
    dsimp only [R, sourceKPJacquetFrequencyRadius]
    push_cast
    omega
  have haR : a ∈ B (R : ℤ) := sourceKPJacquetSelfDual_ball_mono K P (by omega) ha
  have hNR : N ≤ R := by dsimp only [R, sourceKPJacquetFrequencyRadius]; omega
  have hza : (z : L) * a = b := by dsimp only [a]; field_simp [z.ne_zero]
  have hψa : ψ₀ (-((z : L) * a)) ≠ 1 := by
    rw [hza, AddChar.map_neg_eq_inv]
    exact fun h => hψ (by simpa only [inv_inv, inv_one] using congrArg Inv.inv h)
  have hOuter := sourceKPJacquet_open_cell_fixed_shift_at K hζ P ρ hUpper hCube f M N R hNR hTiny
    (fun t ht => by simpa only [one_mul] using (hFix t ht 1).2) a ha
  have hI := sourceKPJacquetSelfDual_truncation_stabilizes K P (E z f) R a haR _ hψa
    (fun r => sourceKPJacquetFrequencyIntegrand_integrableOn K hζ P ρ e z f N (fun t ht g => (hFix t ht g).1) r)
    (fun y hy => sourceKPJacquetFrequencyIntegrand_shift K hζ P ρ e z f y a (hOuter y hy))
  refine eventually_atTop.mpr ⟨R, fun r hr => ?_⟩
  exact congrArg e.symm (hI r hr)

end
end ArtinMatthews

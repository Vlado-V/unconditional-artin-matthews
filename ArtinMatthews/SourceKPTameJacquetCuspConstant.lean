module

public import ArtinMatthews.SourceKPTameJacquetSignedIntegrability


set_option backward.privateInPublic true
@[expose] public section

/-! The actual spherical integrand before its additive phase is
constant on every exterior additive coset of a sufficiently large
Jacquet ball. The valuation and the unit residue in the exact
Bruhat formula are both preserved by the small relative shift. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain SourcePhysical QuadraticWeil VaryingKummerAnalytic
open scoped NumberField SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P

theorem sourceKPTameJacquetPoint_add_of_outside (e : ℤ) (R : ℕ) (hR : -e ≤ (R : ℤ))
    (x t : L) (hx : WithZero.exp (R : ℤ) < ν₀ x) (ht : ν₀ t ≤ WithZero.exp (R : ℤ)) :
    sourceKPTameJacquetPoint K hζ S₀ P e (x + t) = sourceKPTameJacquetPoint K hζ S₀ P e x := by
  let ν := ν₀
  have hx₀ : ν x ≠ 0 := ne_of_gt ((pos_iff_ne_zero.mpr WithZero.exp_ne_zero).trans hx)
  let k := WithZero.log (ν x)
  have hLog : (R : ℤ) < k := WithZero.exp_lt_exp.mp (hx.trans_eq (WithZero.exp_log hx₀).symm)
  let l := (k + e).toNat
  let n := (l : ℤ) - e
  have hn : n = k := by dsimp only [n, l]; omega
  let a := (π₀ : L) ^ n
  let y := a * x
  let z := a * t
  have hνa : ν a = WithZero.exp (-n) := sourceJacquetFrequency_valuation K P.val (π₀ : L) hπ₀ n
  have hνx : ν x = WithZero.exp n := by rw [hn, WithZero.exp_log hx₀]
  have hy : ν y = 1 := by
    dsimp only [y]
    rw [map_mul, hνa, hνx, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  have hz : ν z < 1 := by
    have ha : 0 < ν a := ν.pos_iff.mpr (zpow_ne_zero n (Units.ne_zero π₀))
    have hh := mul_lt_mul_of_pos_left (ht.trans_lt hx) ha
    rw [← map_mul ν a t, ← map_mul ν a x] at hh
    change ν z < ν y at hh
    rwa [hy] at hh
  have hyz : ν (y + z) = 1 := (ν.map_add_eq_of_lt_left (hz.trans_eq hy.symm)).trans hy
  let v := Units.mk0 y (sourceKPVal_eq_one_ne_zero ν hy)
  let w := Units.mk0 (y + z) (sourceKPVal_eq_one_ne_zero ν hyz)
  have hpow : (π₀ : L) ^ e * (π₀ : L) ^ (-(l : ℤ)) * a = 1 := by
    dsimp only [a]
    rw [← zpow_add₀ (Units.ne_zero π₀), ← zpow_add₀ (Units.ne_zero π₀),
      show e + -(l : ℤ) + n = 0 by dsimp only [n]; omega, zpow_zero]
  have hscale (q : L) : (π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * (a * q)) = q := by
    calc
      _ = ((π₀ : L) ^ e * (π₀ : L) ^ (-(l : ℤ)) * a) * q := by simp only [mul_assoc]
      _ = _ := by rw [hpow, one_mul]
  have hv : (π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * (v : L)) = x := hscale x
  have hw : (π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * (w : L)) = x + t := by
    change (π₀ : L) ^ e * ((π₀ : L) ^ (-(l : ℤ)) * (a * x + a * t)) = x + t
    rw [← mul_add, hscale]
  let s : sourceJacquetIntegers K P.val := ⟨z, (adic_mem_integer_iff K P.val z).mpr
    ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P.val).mpr hz.le)⟩
  let χ := sourceJacquetShellCharacter K P.val χ₀ l
  have hweight := sourceJacquetWeight_translate_small K P.val χ y s
    (Valued.toNormedField.norm_lt_one_iff.mpr hz)
  change sourceJacquetWeight K P.val χ (y + z) = sourceJacquetWeight K P.val χ y at hweight
  have h₁ := sourceKPTameJacquetPoint_scaled_shell K hζ S₀ P e l v hy
  have h₂ := sourceKPTameJacquetPoint_scaled_shell K hζ S₀ P e l w hyz
  rw [hv, show (v : L) = y from rfl] at h₁
  rw [hw, show (w : L) = y + z from rfl] at h₂
  rw [h₂, h₁]
  change (_ * sourceJacquetWeight K P.val χ (y + z)) • (_ : ZMod 3 → ℂ) =
    (_ * sourceJacquetWeight K P.val χ y) • _
  rw [hweight]

end
end ArtinMatthews

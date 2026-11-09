module

public import ArtinMatthews.SourceFiniteBallIdeal
public import ArtinMatthews.SIntegerPrincipalQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! A literal finite ball ideal surjects onto an exterior quotient of the
actual localization: a power of the principalizing denominator puts
all integral representatives in the ball ideal, and is a quotient unit. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain FractionalIdeal SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀

theorem sourcePrincipalDenominator_valuation_exterior (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ S) : P.valuation K (d : K) = 1 := by
  apply (P.valuation_eq_one_iff_notMem (K := K)).mpr
  intro h
  exact hP ((mem_denominatorSupport _ (principalizingDenominator_ne_zero S₀) P).mpr h)

theorem sourcePrincipalDenominator_power_mem_ballIdeal (e : S → ℤ) :
    ∃ n : ℕ, (d : K) ^ n ∈ sourceFiniteBallIdeal K S e := by
  let n := (Finset.univ : Finset S).sup (fun v => (e v).toNat)
  refine ⟨n, (sourceFiniteBallIdeal_mem_iff K S e _).mpr ⟨?_, ?_⟩⟩
  · intro P hP
    rw [map_pow, sourcePrincipalDenominator_valuation_exterior K S₀ P hP, one_pow]
  · intro v
    change Valued.v (((d : K) ^ n : K) : v.val.adicCompletion K) ≤ WithZero.exp (-(e v))
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow]
    let a := v.val.valuation K (d : K)
    have ha : a ≠ 0 := (Valuation.ne_zero_iff _).mpr
      ((IsFractionRing.injective (𝓞 K) K).ne (principalizingDenominator_ne_zero S₀))
    have hlt : a < 1 := (v.val.valuation_lt_one_iff_mem (K := K) d).mpr
      ((mem_denominatorSupport _ (principalizingDenominator_ne_zero S₀) v.val).mp v.property)
    have hlog : WithZero.log a < 0 := by
      rw [← WithZero.exp_lt_one_iff, WithZero.exp_log ha]
      exact hlt
    have hnat : (e v).toNat ≤ n := Finset.le_sup (f := fun v => (e v).toNat) (Finset.mem_univ v)
    have hne : e v ≤ (n : ℤ) := by omega
    change a ^ n ≤ _
    rw [← WithZero.exp_log ha, ← WithZero.exp_nsmul, WithZero.exp_le_exp]
    change (n : ℤ) * WithZero.log a ≤ -(e v)
    calc
      _ ≤ (n : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg n)
      _ ≤ _ := by omega

def sourcePrincipalBallIdealToInteger (e : S → ℤ) :
    sourceFiniteBallIdeal K S e →+ OS where
  toFun x := ⟨(x : K), ((sourceFiniteBallIdeal_mem_iff K S e _).mp x.property).1⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem sourcePrincipalBallIdealToInteger_val (e : S → ℤ)
    (x : sourceFiniteBallIdeal K S e) :
    ((sourcePrincipalBallIdealToInteger K S₀ e x : OS) : K) = (x : K) := rfl

def sourcePrincipalBallIdealToQuotient (e : S → ℤ) (M : Ideal (𝓞 K)) :
    sourceFiniteBallIdeal K S e →+ (OS ⧸ M.map (algebraMap (𝓞 K) OS)) :=
  (Ideal.Quotient.mk _).toAddMonoidHom.comp (sourcePrincipalBallIdealToInteger K S₀ e)

theorem sourcePrincipalBallIdealToQuotient_surjective (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d})) :
    Function.Surjective (sourcePrincipalBallIdealToQuotient K S₀ e M) := by
  let : IsLocalization.Away d OS := principalIntegerRing_isLocalization S₀
  let q := Ideal.Quotient.mk (M.map (algebraMap (𝓞 K) OS))
  intro z
  obtain ⟨n, hn⟩ := sourcePrincipalDenominator_power_mem_ballIdeal K S₀ e
  have hdu : IsUnit (algebraMap (𝓞 K) OS (d ^ n)) :=
    IsLocalization.map_units OS (⟨d ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers d)
  obtain ⟨u, hu⟩ := hdu.map q
  obtain ⟨b, hb⟩ := (principalQuotientEquiv S₀ M hc).surjective (↑u⁻¹ * z)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [principalQuotientEquiv_mk] at hb
  have hx : (d : K) ^ n * (b : K) ∈ sourceFiniteBallIdeal K S e := by
    rw [mul_comm]
    exact (sourceFiniteBallIdeal K S e).val.smul_mem b hn
  let x : sourceFiniteBallIdeal K S e := ⟨_, hx⟩
  refine ⟨x, ?_⟩
  have he : sourcePrincipalBallIdealToInteger K S₀ e x =
      algebraMap (𝓞 K) OS (d ^ n) * algebraMap (𝓞 K) OS b := by
    apply Subtype.ext
    change (d : K) ^ n * (b : K) = (algebraMap (𝓞 K) K (d ^ n)) * (b : K)
    rw [map_pow]
  change q (sourcePrincipalBallIdealToInteger K S₀ e x) = z
  rw [he, map_mul, ← hu, hb, u.mul_inv_cancel_left]

end
end ArtinMatthews.SourcePhysical

module

public import ArtinMatthews.GiantWindowArithmetic
public import ArtinMatthews.GiantActualRoughSieve
public import ArtinMatthews.PrimeExtractionTupleBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The large-factor term of Proposition 6.1, indexed by its actual
giant prime and positive cofactor. The shifted Hecke coefficient and
divisibility condition stay on the product. -/

noncomputable section
namespace ArtinMatthews

open Filter
open OAI OAI.SevenEighths
open scoped BigOperators Topology

theorem giantSampling_cofactor_upper {x ε T : ℝ} (hx : 0 < x) {ℓ k : ℕ}
    (hℓ : ℓ ∈ giantPrimeWindow x ε) (hprod : (ℓ : ℝ) * (k : ℝ) ≤ T * x) :
    (k : ℝ) ≤ T * x ^ ε := by
  have hlo := ((mem_giantPrimeWindow hx.le).mp hℓ).2.1
  have hpow : x ^ (1 - ε) * x ^ ε = x := by
    rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
  have hle : x ^ (1 - ε) * (k : ℝ) ≤ x ^ (1 - ε) * (T * x ^ ε) := by
    calc
      _ ≤ (ℓ : ℝ) * (k : ℝ) := mul_le_mul_of_nonneg_right hlo.le (Nat.cast_nonneg _)
      _ ≤ T * x := hprod
      _ = T * (x ^ (1 - ε) * x ^ ε) := congrArg (T * ·) hpow.symm
      _ = _ := by ring
  by_contra! h
  exact (not_lt_of_ge hle) (mul_lt_mul_of_pos_left h (Real.rpow_pos_of_pos hx (1 - ε)))

theorem giantSampling_cofactor_lower {x ε : ℝ} (hx : 0 < x) {ℓ k : ℕ}
    (hℓ : ℓ ∈ giantPrimeWindow x ε) (hprod : x < (ℓ : ℝ) * (k : ℝ)) :
    x ^ (ε / 2) < (k : ℝ) := by
  have hhi := ((mem_giantPrimeWindow hx.le).mp hℓ).2.2
  have hpow : x ^ (1 - ε / 2) * x ^ (ε / 2) = x := by
    rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]
  have hlt : x ^ (1 - ε / 2) * x ^ (ε / 2) < x ^ (1 - ε / 2) * (k : ℝ) := by
    rw [hpow]
    exact hprod.trans_le (mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg _))
  by_contra! h
  exact (not_le_of_gt hlt) (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le _))

def giantCubicSamplingKernel (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (Φ : ℝ → ℝ) (x : ℝ) (r u : ℕ) : ℂ :=
  if r ∣ u + 1 then
    (Φ ((u : ℝ) / x) : ℂ) * idealThetaCoeff η (u + 1) * χ (u + 1)
  else 0

def giantCubicSamplingGiantSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ) (r : ℕ) : ℂ :=
  ∑ u ∈ Finset.Icc 1 ⌊2 * x⌋₊,
    (((giantPrimeFactors u x ε).card : ℝ) : ℂ) * (H u * giantCubicSamplingKernel η χ Φ x r u)

def giantCubicSamplingCofactorSum (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (r : ℕ) (K : Finset ℕ) : ℂ :=
  ∑ ℓ ∈ giantPrimeWindow x ε, ∑ k ∈ K, H k * giantCubicSamplingKernel η χ Φ x r (ℓ * k)

theorem giantCubicSamplingGiantSum_eq_cofactors (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (r : ℕ)
    {ε x : ℝ} (hx : 0 < x) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hH : ∀ ℓ ∈ giantPrimeWindow x ε, ∀ k, H (ℓ * k) = H k) :
    giantCubicSamplingGiantSum η χ H Φ ε x r =
      giantCubicSamplingCofactorSum η χ H Φ ε x r (Finset.Icc 1 ⌊2 * x ^ ε⌋₊) := by
  classical
  let U := Finset.Icc 1 ⌊2 * x⌋₊
  let K := Finset.Icc 1 ⌊2 * x ^ ε⌋₊
  let f := giantCubicSamplingKernel η χ Φ x r
  have hrow (u : ℕ) (hu : u ∈ U) :
      (((giantPrimeFactors u x ε).card : ℝ) : ℂ) * (H u * f u) =
        ∑ ℓ ∈ giantPrimeWindow x ε, if ℓ ∣ u then H u * f u else 0 := by
    rw [giantPrimeFactors_eq_window_filter (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1) hx.le,
      ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    push_cast
    rfl
  unfold giantCubicSamplingGiantSum giantCubicSamplingCofactorSum
  change (∑ u ∈ U, _ ) = ∑ ℓ ∈ giantPrimeWindow x ε, ∑ k ∈ K, H k * f (ℓ * k)
  rw [Finset.sum_congr rfl hrow, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ hℓ
  rw [← Finset.sum_filter]
  have hℓpos := ((mem_giantPrimeWindow hx.le).mp hℓ).1.pos
  have hroweq :
      (∑ u ∈ U.filter (fun u => ℓ ∣ u), H u * f u) =
        ∑ k ∈ K.filter (fun k => ℓ * k ≤ ⌊2 * x⌋₊), H k * f (ℓ * k) := by
    symm
    apply Finset.sum_bij (fun k _ => ℓ * k)
    · intro k hk
      obtain ⟨hkK, htop⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.mul_pos hℓpos (Finset.mem_Icc.mp hkK).1, htop⟩, dvd_mul_right _ _⟩
    · intro k _ j _ h
      exact Nat.eq_of_mul_eq_mul_left hℓpos h
    · intro u hu
      obtain ⟨huU, k, h⟩ := Finset.mem_filter.mp hu
      obtain ⟨hpos, htop⟩ := Finset.mem_Icc.mp huU
      have hk : 0 < k := Nat.pos_of_ne_zero (fun hz => by simp [h, hz] at hpos)
      have hreal : (ℓ : ℝ) * (k : ℝ) ≤ 2 * x := by
        rw [← Nat.cast_mul, ← h]
        exact (Nat.cast_le.mpr htop).trans (Nat.floor_le (by positivity))
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨hk, Nat.le_floor (giantSampling_cofactor_upper hx hℓ hreal)⟩, h ▸ htop⟩, h.symm⟩
    · intro k _hk
      rw [hH ℓ hℓ k]
  rw [hroweq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases htop : ℓ * k ≤ ⌊2 * x⌋₊
  · simp only [htop, ite_true]
  · have hzero : Φ (((ℓ * k : ℕ) : ℝ) / x) = 0 := by
      by_contra hn
      apply htop
      exact Nat.le_floor (((div_lt_iff₀ hx).mp (hs hn).2).le)
    simp only [Nat.cast_mul] at hzero
    simp [htop, f, giantCubicSamplingKernel, hzero]

theorem giantSampling_literalArray_giant_invariant_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, e j < 1) {ε : ℝ} (hε : ε < 1) :
    ∀ᶠ x : ℝ in atTop, ∀ ℓ ∈ giantPrimeWindow x ε, ∀ k : ℕ,
      literalMarkedArrayWeight e x (ℓ * k) = literalMarkedArrayWeight e x k := by
  have hsmall := eventually_all.mpr fun j => marked_band_below_giant_eventually (he j) hε
  filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with x hb hx
  intro ℓ hℓ k
  obtain ⟨hprime, hlo, _⟩ := (mem_giantPrimeWindow hx).mp hℓ
  unfold literalMarkedArrayWeight divisorWeight
  apply Finset.prod_congr rfl
  intro j _hj
  have hset : activeDivisors (markedLogPowerBand (e j) x) (ℓ * k) =
      activeDivisors (markedLogPowerBand (e j) x) k := by
    ext p
    simp only [activeDivisors, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hdiv⟩
      have hpprime := (mem_markedLogPowerBand.mp hp).1
      refine ⟨hp, (hpprime.dvd_mul.mp hdiv).resolve_left ?_⟩
      intro h
      have heq := (Nat.prime_dvd_prime_iff_eq hpprime hprime).mp h
      exact (not_lt_of_ge (hb j p hp)) (heq ▸ hlo)
    · rintro ⟨hp, hdiv⟩
      exact ⟨hp, dvd_mul_of_dvd_right hdiv ℓ⟩
  simp only [bandWeight, bandCount, hset]

end ArtinMatthews

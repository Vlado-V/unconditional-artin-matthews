module

public import ArtinMatthews.PrimeExtractionPrimeRoughIdentity
public import ArtinMatthews.PrimeExtractionBilinearExpansion
public import ArtinMatthews.GiantCharacterFactorizations


set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary fixed-character prime extraction. These are the actual rough
and prime sums with the literal marking array, rather than the cubic theta
coefficient. Repeated-prime errors are removed with every logarithmic saving;
the remaining finite hyperbola sums retain the original factorials. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators Asymptotics

theorem giant_character_tuple_squarefree {q : ℕ} (χ : DirichletCharacter ℂ q)
    {j n : ℕ} (hn : Squarefree n) {z : ℝ} (hr : MarkedRoughAbove z n)
    (hj : n.primeFactorsList.length = j) :
    roughPrimeTupleCoefficient (fun p => χ p) j n z = (j.factorial : ℂ) * χ n := by
  classical
  unfold roughPrimeTupleCoefficient
  have ht : ∀ l ∈ roughOrderedPrimeFactorizations j n z,
      (l.map (fun p : ℕ => χ p)).prod = χ n := by
    intro l hl
    have hprod := ((mem_roughOrderedPrimeFactorizations j n z l).mp hl).2.1
    simpa only [one_mul, List.map_const', List.prod_replicate, one_pow, mul_one, hprod] using
      giant_character_list_product χ (fun _ => 1) l
  rw [Finset.sum_congr rfl ht]
  rw [roughOrderedPrimeFactorizations_eq hn.ne_zero hr hj, Finset.sum_const,
    orderedPrimeFactorizations_card hn, hj, nsmul_eq_mul]

def giantOrdinaryCompositeCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n ≠ 1 ∧ ¬n.Prime then χ n else 0

theorem giant_character_composite_squarefree {q : ℕ} (χ : DirichletCharacter ℂ q)
    (J : ℕ) {n : ℕ} (hn : Squarefree n) {z : ℝ} (hr : MarkedRoughAbove z n)
    (hJ : n.primeFactorsList.length ≤ J) :
    giantOrdinaryCompositeCoefficient χ n = roughCompositeCoefficient (fun p => χ p) J n z := by
  classical
  unfold roughCompositeCoefficient giantOrdinaryCompositeCoefficient
  by_cases hlen : n.primeFactorsList.length ∈ Finset.Icc 2 J
  · have hc : n ≠ 1 ∧ ¬n.Prime :=
      (primeFactorsList_length_ge_two_iff hn.ne_zero).mp (Finset.mem_Icc.mp hlen).1
    rw [ite_eq_left hc, Finset.sum_eq_single n.primeFactorsList.length]
    · rw [giant_character_tuple_squarefree χ hn hr rfl]
      have hf : (n.primeFactorsList.length.factorial : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero _
      field_simp
    · intro j _ hj
      rw [roughPrimeTupleCoefficient_eq_zero_of_length_ne _ _ _ _ hj.symm, zero_div]
    · exact fun h => (h hlen).elim
  · have hc : ¬(n ≠ 1 ∧ ¬n.Prime) := by
      intro h
      exact hlen (Finset.mem_Icc.mpr ⟨(primeFactorsList_length_ge_two_iff hn.ne_zero).mpr h, hJ⟩)
    rw [ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [roughPrimeTupleCoefficient_eq_zero_of_length_ne _ _ _ _
      (fun h => hlen (h ▸ hj)), zero_div]

theorem giantOrdinaryCompositeCoefficient_norm_le {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) : ‖giantOrdinaryCompositeCoefficient χ n‖ ≤ 1 := by
  unfold giantOrdinaryCompositeCoefficient
  split_ifs
  · exact χ.norm_le_one _
  · norm_num

theorem giant_character_composite_bounds_eventually {q : ℕ}
    (χ : DirichletCharacter ℂ q) (T : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ T*x →
      MarkedRoughAbove (x^γ) n →
      (Squarefree n → giantOrdinaryCompositeCoefficient χ n =
        roughCompositeCoefficient (fun p => χ p) ⌈2/γ⌉₊ n (x^γ)) ∧
      ‖giantOrdinaryCompositeCoefficient χ n -
        roughCompositeCoefficient (fun p => χ p) ⌈2/γ⌉₊ n (x^γ)‖ ≤
          1 + ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊, (1 : ℝ)^j := by
  filter_upwards [marked_rough_factor_and_divisor_count_eventually T hγ] with x hx
  intro n hn hnT hr
  refine ⟨fun hs => giant_character_composite_squarefree χ _ hs hr (hx n hn hnT hr).1, ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add
    (giantOrdinaryCompositeCoefficient_norm_le χ n)
    (roughCompositeCoefficient_norm_le _ _ _ _ zero_le_one (fun p _ _ => χ.norm_le_one p)))

def giantOrdinaryRoughSum {J : Type*} [Fintype J] (e : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughPositiveUpTo ⌊T*x⌋₊ (x^γ), markedExtractionWeight e G Φ x n * χ n

def giantOrdinaryPrimeSum {J : Type*} [Fintype J] (e : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T x : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊T*x⌋₊).filter Nat.Prime, markedExtractionWeight e G Φ x n * χ n

def giantOrdinaryCompositeSum {J : Type*} [Fintype J] (e : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughPositiveUpTo ⌊T*x⌋₊ (x^γ),
    markedExtractionWeight e G Φ x n * giantOrdinaryCompositeCoefficient χ n

def giantOrdinaryExpandedSum {J : Type*} [Fintype J] (e : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T*x⌋₊, markedExtractionWeight e G Φ x n *
    roughCompositeCoefficient (fun p => χ p) ⌈2/γ⌉₊ n (x^γ)

theorem giant_ordinary_rough_sub_prime_eq {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) {a b γ : ℝ} (T : ℝ) (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a b) (hγ : γ < 1) :
    ∀ᶠ x : ℝ in atTop, giantOrdinaryRoughSum e χ G Φ T γ x -
      giantOrdinaryPrimeSum e χ G Φ T x = giantOrdinaryCompositeSum e χ G Φ T γ x := by
  classical
  have hzero : Φ 0 = 0 := by
    by_contra hh
    exact (not_le_of_gt ha) (hsupp hh).1
  filter_upwards [markedExtractionWeight_prime_rough_eventually e G Φ ha hsupp hγ] with x hx
  have hw1 : markedExtractionWeight e G Φ x 1 = 0 := by
    simp only [markedExtractionWeight, Nat.sub_self, Nat.cast_zero, zero_div,
      hzero, Complex.ofReal_zero, zero_mul]
  unfold giantOrdinaryRoughSum giantOrdinaryPrimeSum giantOrdinaryCompositeSum
    roughPositiveUpTo giantOrdinaryCompositeCoefficient
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hr : MarkedRoughAbove (x^γ) n
  · by_cases hp : n.Prime
    · simp [hr, hp]
    · by_cases hn : n = 1
      · subst n
        simp [hw1]
      · simp [hr, hp, hn]
  · have hw : n.Prime → markedExtractionWeight e G Φ x n = 0 := by
      intro hp
      by_contra hw
      exact hr (hx n hp hw)
    by_cases hp : n.Prime
    · simp [hr, hp, hw hp]
    · simp [hr, hp]

/-- The ordinary composite expansion has only the actual rough squareful
error. Its coefficient is bounded independently of x. -/
theorem giant_ordinary_composite_expansion_isLittleO {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    (fun x => giantOrdinaryCompositeSum e χ G Φ T γ x -
      giantOrdinaryExpandedSum e χ G Φ T γ x) =o[atTop]
        (fun x : ℝ => x * (Real.log x)^(-A)) := by
  classical
  let b (x : ℝ) (n : ℕ) := giantOrdinaryCompositeCoefficient χ n -
    roughCompositeCoefficient (fun p => χ p) ⌈2/γ⌉₊ n (x^γ)
  have hb := giant_character_composite_bounds_eventually χ T hγ
  have hs := markedSquarefulCoefficientSum_isLittleO e he b G hCG hG Φ hΦ hT hγ
    (hb.mono (fun x hx n hn hnT hr => (hx n hn hnT hr).2)) A
  apply hs.congr' _ Filter.EventuallyEq.rfl
  filter_upwards [hb, eventually_gt_atTop (0 : ℝ)] with x hbx hx
  have herr : markedSquarefulCoefficientSum e b G Φ T γ x =
      ∑ n ∈ roughPositiveUpTo ⌊T*x⌋₊ (x^γ), markedExtractionWeight e G Φ x n * b x n := by
    unfold markedSquarefulCoefficientSum
    apply Finset.sum_subset
    · intro n hn
      obtain ⟨hnrange, hn0, hr, _⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0,
        Nat.le_of_lt_succ (Finset.mem_range.mp hnrange)⟩, hr⟩
    · intro n hn hnnot
      obtain ⟨hnI, hr⟩ := Finset.mem_filter.mp hn
      have hn0 : n ≠ 0 := (Finset.mem_Ioc.mp hnI).1.ne'
      have hsq : Squarefree n := by
        by_contra hnsq
        exact hnnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hnI).2), hn0, hr, hnsq⟩)
      have hnT : (n : ℝ) ≤ T*x := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hnI).2).trans
        (Nat.floor_le (mul_nonneg hT hx.le))
      dsimp only [b]
      rw [(hbx n hn0 hnT hr).1 hsq, sub_self, mul_zero]
  rw [herr]
  unfold giantOrdinaryCompositeSum giantOrdinaryExpandedSum
  simp only [b, mul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnnot
  have hr : ¬MarkedRoughAbove (x^γ) n := fun hr => hnnot (Finset.mem_filter.mpr ⟨hn, hr⟩)
  rw [roughCompositeCoefficient_eq_zero_of_not_rough _ _ _ _ hr, mul_zero]

def giantOrdinaryTupleSum {J : Type*} [Fintype J] (e : J → ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ : ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊T*x⌋₊, markedExtractionWeight e G Φ x n *
    (roughPrimeTupleCoefficient (fun p => χ p) j n (x^γ) / j.factorial)

theorem giant_ordinary_expanded_eq_tuple {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) :
    giantOrdinaryExpandedSum e χ G Φ T γ x =
      ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊, giantOrdinaryTupleSum e χ G Φ T γ j x := by
  unfold giantOrdinaryExpandedSum roughCompositeCoefficient giantOrdinaryTupleSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem giant_ordinary_prime_rough_reduction {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, 0 < e j) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {a b T γ : ℝ} (ha : 0 < a)
    (hsupp : Function.support Φ ⊆ Set.Icc a b) (hT : 0 ≤ T)
    (hγ : 0 < γ) (hγ1 : γ < 1) (A : ℝ) :
    (fun x => giantOrdinaryRoughSum e χ G Φ T γ x - giantOrdinaryPrimeSum e χ G Φ T x -
      ∑ j ∈ Finset.Icc 2 ⌈2/γ⌉₊, giantOrdinaryTupleSum e χ G Φ T γ j x) =o[atTop]
        (fun x : ℝ => x * (Real.log x)^(-A)) := by
  apply (giant_ordinary_composite_expansion_isLittleO e he χ G hCG hG Φ hΦ hT hγ A).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [giant_ordinary_rough_sub_prime_eq e χ G Φ T ha hsupp hγ1] with x hx
  rw [hx, giant_ordinary_expanded_eq_tuple]

/-- The exact finite hyperbola reduction for the ordinary coefficient.
The original shifted smooth cutoff, marking weight and j! survive unchanged. -/
theorem giant_ordinary_tuple_bilinear {J : Type*} [Fintype J]
    (e : J → ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (G : ℝ → ℕ → ℂ)
    (Φ : ℝ → ℝ) (T γ x : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    giantOrdinaryTupleSum e χ G Φ T γ j x =
      (∑ mn ∈ (Finset.Ioc 0 ⌊T*x⌋₊ ×ˢ Finset.Ioc 0 ⌊T*x⌋₊).filter
          (fun mn => mn.1*mn.2 ≤ ⌊T*x⌋₊),
        markedExtractionWeight e G Φ x (mn.1*mn.2) *
          roughPrimeFirstCoefficient (fun p => χ p) (x^γ) mn.1 *
          roughPrimeTupleCoefficient (fun p => χ p) (j-1) mn.2 (x^γ)) / j.factorial := by
  have h := roughPrimeTupleCoefficient_bilinear_expansion (fun p => χ p)
    (j-1) ⌊T*x⌋₊ (x^γ) (markedExtractionWeight e G Φ x)
  rw [Nat.sub_add_cancel hj] at h
  unfold giantOrdinaryTupleSum
  simp only [← mul_div_assoc, ← Finset.sum_div]
  exact congrArg (fun z : ℂ => z / j.factorial) h

end ArtinMatthews

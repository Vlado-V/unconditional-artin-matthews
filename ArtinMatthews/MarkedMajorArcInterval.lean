module

public import ArtinMatthews.MarkedMajorArcRiesz
public import ArtinMatthews.MarkedMajorArcRieszSmoothing
public import ArtinMatthews.MarkedMajorArcBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Literal sharp interval estimates for the character Mangoldt coefficients.
The common contour residue cancels exactly; all remaining terms are explicit. -/
namespace ArtinMatthews

open Finset Filter
open scoped Topology BigOperators

lemma marked_floor_interval_sum (a : ℕ → ℂ) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) {N : ℕ} (hN : ⌊v⌋₊ ≤ N) :
    (∑ n ∈ Icc 1 N, a n*(if u < (n:ℝ) ∧ (n:ℝ) ≤ v then 1 else 0)) =
      ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, a n := by
  classical
  have hf : (Icc 1 N).filter (fun n : ℕ => u < (n:ℝ) ∧ (n:ℝ) ≤ v) =
      Ioc ⌊u⌋₊ ⌊v⌋₊ := by
    ext n
    simp only [mem_filter,mem_Icc,mem_Ioc]
    constructor
    · rintro ⟨_,hlo,hhi⟩
      exact ⟨(Nat.floor_lt hu).mpr hlo,Nat.le_floor hhi⟩
    · rintro ⟨hlo,hhi⟩
      exact ⟨⟨by omega,hhi.trans hN⟩,(Nat.floor_lt hu).mp hlo,
        (Nat.le_floor_iff (hu.trans huv)).mp hhi⟩
  rw [← hf,sum_filter]
  apply sum_congr rfl
  intro n hn
  split_ifs <;> simp

noncomputable def markedMajorIntervalError (K C L H ε u v : ℝ) : ℝ :=
  ((1+ε)*(markedMajorRieszError K C L H ((1+ε)*v) +
      markedMajorRieszError K C L H ((1+ε)*u)) +
    markedMajorRieszError K C L H v + markedMajorRieszError K C L H u)/ε +
    (ε*(u+v)+2)*(Real.log ((1+ε)*v)/u)

/-- An unconditional bound for the actual sharp finite interval sum. The
parameters on the right may subsequently be chosen as powers of `log x`. -/
theorem marked_major_mangoldt_interval_error (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) :
    ∃ K C T₀ : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 < T₀ ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q], (q:ℝ) ≤ L^A →
      ∀ (χ : DirichletCharacter ℂ q) (ε u v t H : ℝ),
      0 < ε → 1 ≤ u → u ≤ v → 0 < H → H ≤ |t|/2 →
      2*T₀ ≤ |t| → 2*|t| ≤ Real.exp (b*L) →
      ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorMangoldt χ t n‖ ≤
        markedMajorIntervalError K C L H ε u v := by
  obtain ⟨K,C,T₀,hK,hC,hT₀,hr⟩ := marked_major_mangoldt_riesz_error A b hA hb
  refine ⟨K,C,T₀,hK,hC,hT₀,?_⟩
  filter_upwards [hr] with L hL
  intro q _ hq χ ε u v t H hε hu huv hH hHt htlo hthi
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := hu0.trans_le huv
  let S := Icc 1 ⌊(1+ε)*v⌋₊
  let F : ℂ := -deriv (DirichletCharacter.LFunction χ) (1-(t:ℂ)*Complex.I) /
    DirichletCharacter.LFunction χ (1-(t:ℂ)*Complex.I)
  let R (x : ℝ) := markedMajorRieszSum χ t x
  let E (x : ℝ) := markedMajorRieszError K C L H x
  let P (x : ℝ) := ∑ n ∈ S, markedMajorMangoldt χ t n*(markedSmoothedStep ε x n : ℂ)
  have hR (x : ℝ) (hx : 1 ≤ x) : ‖R x-F‖ ≤ E x :=
    hL q hq χ x t H hx hH hHt htlo hthi
  have hP (x : ℝ) (hux : u ≤ x) (hxv : x ≤ v) :
      ‖P x-F‖ ≤ ((1+ε)*E ((1+ε)*x)+E x)/ε := by
    have hx : 1 ≤ x := hu.trans hux
    have hx0 : 0 < x := hu0.trans_le hux
    have hx' : 1 ≤ (1+ε)*x := by nlinarith
    have hN : ⌊(1+ε)*x⌋₊ ≤ ⌊(1+ε)*v⌋₊ :=
      Nat.floor_mono (mul_le_mul_of_nonneg_left hxv (by positivity))
    have he := marked_smoothed_sum_riesz (markedMajorMangoldt χ t) hε hx0 hN
    change P x = ((1+ε:ℝ):ℂ)*R ((1+ε)*x)/(ε:ℂ)-R x/(ε:ℂ) at he
    rw [he]
    exact marked_common_residue_smoothing_bound hε (hR _ hx') (hR _ hx)
  have hdiff : ‖P v-P u‖ ≤
      ((1+ε)*(E ((1+ε)*v)+E ((1+ε)*u))+E v+E u)/ε := by
    have he : P v-P u=(P v-F)-(P u-F) := by ring
    rw [he]
    exact ((norm_sub_le _ _).trans
      (add_le_add (hP v huv le_rfl) (hP u le_rfl huv))).trans_eq (by ring)
  have heSmooth : (∑ n ∈ S, markedMajorMangoldt χ t n*
      ((markedSmoothedStep ε v n-markedSmoothedStep ε u n : ℝ):ℂ)) = P v-P u := by
    simp only [Complex.ofReal_sub,mul_sub,sum_sub_distrib,P]
  have hN : ⌊v⌋₊ ≤ ⌊(1+ε)*v⌋₊ := Nat.floor_mono (by nlinarith)
  have heSharp := marked_floor_interval_sum (markedMajorMangoldt χ t) hu0.le huv hN
  have hbnd := marked_major_mangoldt_smoothing_error χ t hε hu huv S
  rw [heSmooth,heSharp] at hbnd
  have he : (∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorMangoldt χ t n) =
      (P v-P u)-((P v-P u)-(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorMangoldt χ t n)) := by ring
  calc
    _ ≤ ‖P v-P u‖ + ‖(P v-P u)-(∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊, markedMajorMangoldt χ t n)‖ := by
      conv_lhs => rw [he]
      exact norm_sub_le _ _
    _ ≤ _ := add_le_add hdiff hbnd

end ArtinMatthews

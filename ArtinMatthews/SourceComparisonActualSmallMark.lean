module

public import ArtinMatthews.SourceComparisonSmallMarkReindex
public import ArtinMatthews.SourceComparisonActualModel


set_option backward.privateInPublic true
@[expose] public section

/-! The exact distinguished small group can be removed with a uniformly
negligible squared error on positive prefixes and hence on every dyad. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section

universe u v
variable {J : Type u} [Fintype J] {G : Type v} [Fintype G]

def sourceComparisonActualSmallMarkWeight (e : J → ℝ) {x : ℝ}
    (s : GiantCandidateSmallGroupIndex x) (i : G ↪ GiantCandidateGroupIndex x)
    (a : ℕ) (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) : ℕ → ℂ :=
  sourceComparisonDistinguishedMarkWeight (giantCandidateSmallGroup x s)
    (sourceComparisonActualBands e x i) a (Sum.elim (fun _ => 1) t) q₀ (Sum.elim (fun _ => 1/2) q)
    (fun l => b (fun g => l (.inr g)))

def sourceComparisonActualRemovedSmallMark (e : J → ℝ) {x : ℝ}
    (s : GiantCandidateSmallGroupIndex x) (i : G ↪ GiantCandidateGroupIndex x)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ) : ℕ → ℂ :=
  sourceComparisonRemovedSmallMark (giantCandidateSmallGroup x s)
    (sourceComparisonActualBands e x i) (Sum.elim (fun _ => 1) t) q₀ (Sum.elim (fun _ => 1/2) q)
    (fun l => b (fun g => l (.inr g)))

theorem sourceComparisonActualSmallMarkWeight_eq (e : J → ℝ) {x : ℝ}
    (s : GiantCandidateSmallGroupIndex x) (i : G ↪ GiantCandidateGroupIndex x)
    (hout : (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i)
    (a : ℕ) (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ) :
    sourceComparisonActualSmallMarkWeight e s i a t q₀ q b =
      sourceComparisonInertActiveMarks e x
        (giantCandidateGroup x ∘ sourceComparisonDistinguishedGroupEmbedding s i hout)
        (Sum.elim (fun _ => a) t) (Sum.elim (fun _ => q₀) q) (fun l => b (fun g => l (.inr g))) := by
  rw [sourceComparisonDistinguishedGroupEmbedding_band]
  funext n
  exact sourceComparisonDistinguishedMarkWeight_inert_eq e x (giantCandidateSmallGroup x s)
    (giantCandidateGroup x ∘ i) a t q₀ q b n

theorem sourceComparisonActualRemovedSmallMark_eq_sum (e : J → ℝ) {x : ℝ}
    (s : GiantCandidateSmallGroupIndex x) (i : G ↪ GiantCandidateGroupIndex x)
    (t : G → ℕ) (q₀ : ℝ) (q : G → ℝ) (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    sourceComparisonActualRemovedSmallMark e s i t q₀ q b n =
      (bandReciprocalMass (giantCandidateSmallGroup x s) : ℂ)⁻¹ *
        ∑ p ∈ activeDivisors (giantCandidateSmallGroup x s) n,
          sourceComparisonActualSmallMarkWeight e s i 0 t q₀ q b (n/p) := rfl

theorem sourceComparisonActualSmallMark_square_error_eventually (e : J → ℝ)
    (he : ∀ j, (1/10:ℝ) < e j ∧ e j < 1/5) (heinj : Function.Injective e)
    (m : ℕ) {r : ℝ} (hr : (1/2:ℝ) ≤ r) (hr₁ : r < 1) (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop, ∀ {G : Type v} [Fintype G]
      (s : GiantCandidateSmallGroupIndex x) (i : G ↪ GiantCandidateGroupIndex x),
      (Sum.inl s : GiantCandidateGroupIndex x) ∉ Set.range i →
      ∀ (t : G → ℕ), (∀ g, t g ≤ m) →
      ∀ (q₀ : ℝ), 0 ≤ q₀ → q₀ ≤ r →
      ∀ (q : G → ℝ), (∀ g, 0 ≤ q g ∧ q g ≤ r) →
      ∀ (b : ((g : G) → Fin (t g) → ℕ) → ℂ),
        (∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t, ‖b l‖ ≤ 1) →
      let W := sourceComparisonActualSmallMarkWeight e s i 1 t q₀ q b
      let W' := sourceComparisonActualRemovedSmallMark e s i t q₀ q b
      (∀ n, ‖W' n‖ ≤ ‖W n‖ ∧ ‖W n‖ ≤ (Real.log x) ^ D) ∧
      ∀ N : ℕ, (∑ n ∈ Ioc 0 N, ‖W n - W' n‖ ^ 2) ≤ (N : ℝ) * (Real.log x) ^ (-A) := by
  obtain ⟨D, E, K, hD, hE, hK, hmodel⟩ :=
    sourceComparisonActualInertActiveModel_eventually.{u,v} e he heinj (m+1) hr hr₁ 0
  refine ⟨D, hD, ?_⟩
  have hgrowth := Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<28/100)).comp Real.tendsto_log_atTop)
  have hdecay := (rpow_mul_exp_neg_rpow_tendsto (2*D+A) (by norm_num : (0:ℝ)<28/100)
    zero_lt_one).const_mul 16
  filter_upwards [hmodel, sourceComparisonActualBands_geometry_eventually.{u,v} e he heinj,
    hgrowth.eventually (eventually_ge_atTop (4:ℝ)),
    Real.tendsto_log_atTop.eventually ((by simpa only [mul_zero] using hdecay :
      Tendsto (fun L : ℝ => 16 * (L ^ (2*D+A) * Real.exp (-1 * L ^ (28/100:ℝ)))) atTop (𝓝 0)).eventually
      (gt_mem_nhds zero_lt_one)),
    eventually_gt_atTop (1:ℝ), Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with x hmodel hG h4 hdecay hx hL
  intro G _ s i hout t ht q₀ hq₀ hq₀r q hq b hb
  let i' := sourceComparisonDistinguishedGroupEmbedding s i hout
  let S := giantCandidateSmallGroup x s
  let P := sourceComparisonActualBands e x i
  let u : J ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let r₁ : J ⊕ G → ℝ := Sum.elim (fun _ => 1/2) q
  let b₁ (l : (g : J ⊕ G) → Fin (u g) → ℕ) := b (fun g => l (.inr g))
  let u' : Unit ⊕ G → ℕ := Sum.elim (fun _ => 1) t
  let q' : Unit ⊕ G → ℝ := Sum.elim (fun _ => q₀) q
  let b' (l : (g : Unit ⊕ G) → Fin (u' g) → ℕ) := b (fun g => l (.inr g))
  let L := Real.log x
  let W := sourceComparisonActualSmallMarkWeight e s i 1 t q₀ q b
  let W' := sourceComparisonActualRemovedSmallMark e s i t q₀ q b
  have hu (g : Unit ⊕ G) : u' g ≤ m+1 := by
    rcases g with g | g
    · exact Nat.le_add_left 1 m
    · exact (ht g).trans (Nat.le_succ m)
  have hq' (g : Unit ⊕ G) : 0 ≤ q' g ∧ q' g ≤ r := by
    rcases g with g | g
    · exact ⟨hq₀, hq₀r⟩
    · exact hq g
  have hb' : ∀ l ∈ sourceComparisonMarkChoices (giantCandidateGroup x ∘ i') u', ‖b' l‖ ≤ 1 := by
    intro l hl
    have hl' := (mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i') u' l).mp hl
    exact hb _ ((mem_sourceComparisonMarkChoices (giantCandidateGroup x ∘ i) t (fun g => l (.inr g))).mpr
      ⟨fun g z => hl'.1 (.inr g) z, fun g => hl'.2 (.inr g)⟩)
  have hW (n : ℕ) : ‖W n‖ ≤ L ^ D := by
    rw [show W = sourceComparisonActualSmallMarkWeight e s i 1 t q₀ q b from rfl,
      sourceComparisonActualSmallMarkWeight_eq e s i hout]
    exact (hmodel i' u' hu q' hq' b' hb').1 n
  have hS (p : ℕ) (hp : p ∈ S) := giantCandidateSmallGroup_range hx hL hp
  have hP (g : J ⊕ G) (p : ℕ) (hp : p ∈ P g) : p.Prime :=
    ((hG i).2.2.1 p (mem_biUnion.mpr ⟨g, mem_univ _, hp⟩)).1
  have hdis (g : J ⊕ G) : Disjoint S (P g) := by
    rcases g with j | g
    · exact @(hG i').1 (.inr (.inl ())) (.inl j) (by simp)
    · exact @(hG i').1 (.inr (.inl ())) (.inr (.inr g)) (by simp)
  have hV : 0 < bandReciprocalMass S :=
    (by positivity : 0 < Real.log 2 / 2).trans ((hG i').2.1 (.inr (.inl ()))).1
  have hq₀' : 0 ≤ q₀ ∧ q₀ ≤ 1 := ⟨hq₀, hq₀r.trans hr₁.le⟩
  have hW' (n : ℕ) : ‖W' n‖ ≤ ‖W n‖ :=
    sourceComparisonRemovedSmallMark_norm_le S P u q₀ r₁ b₁ (fun p hp => (hS p hp).1)
      hP hdis hV hq₀' n
  refine ⟨fun n => ⟨hW' n, hW n⟩, ?_⟩
  intro N
  have hdiff (n : ℕ) (_ : n ∈ Ioc 0 N) : ‖W n - W' n‖ ≤ 2 * L ^ D :=
    (norm_sub_le _ _).trans ((add_le_add (hW n) ((hW' n).trans (hW n))).trans_eq (by ring))
  have hbase := sourceComparisonOneSmallMark_square_error S P u q₀ r₁ b₁ (fun p hp => (hS p hp).1)
    hP hdis N (2 * L ^ D) hdiff
  have hrec := marked_reciprocal_square_tail_le S h4 (fun p hp => (hS p hp).2.1)
  have hrec' : (∑ p ∈ S, 1 / (p : ℝ)^2) ≤ 4 * Real.exp (-(L ^ (28/100:ℝ))) := by
    simpa only [Function.comp_apply, L, Real.exp_neg, div_eq_mul_inv] using hrec
  have hL₀ : 0 < L := zero_lt_one.trans_le hL
  have habsorb : 4 * Real.exp (-(L ^ (28/100:ℝ))) * (2 * L ^ D) ^ 2 ≤ L ^ (-A) := by
    rw [Real.rpow_neg hL₀.le, ← one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hL₀ A)).mpr
    have hdec : 16 * (L ^ (2*D+A) * Real.exp (-(L ^ (28/100:ℝ)))) ≤ 1 := by
      simpa only [neg_mul, one_mul] using hdecay.le
    convert hdec using 1
    rw [Real.rpow_add hL₀ (2*D) A, mul_comm (2:ℝ) D, Real.rpow_mul hL₀.le, Real.rpow_two]
    ring
  calc
    _ ≤ (N : ℝ) * (∑ p ∈ S, 1 / (p : ℝ)^2) * (2 * L ^ D) ^ 2 := hbase
    _ ≤ (N : ℝ) * (4 * Real.exp (-(L ^ (28/100:ℝ)))) * (2 * L ^ D) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrec' (Nat.cast_nonneg N)) (sq_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg N)

end
end ArtinMatthews

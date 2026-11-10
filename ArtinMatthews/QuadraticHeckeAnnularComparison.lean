module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import ArtinMatthews.QuadraticHeckeTagAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Annular enlargement by tags of a controlled norm. A factor-three-half
row split allows tags of a fixed relative width without crossing the
target annulus. Both finite row pieces keep the original columns. -/
namespace ArtinMatthews.QuadraticScale

open scoped BigOperators

noncomputable section
variable {P : Type*}

def supportNorm (w : P → ℝ) (r : Finset P) : ℝ :=
  ∏ p ∈ r, w p

theorem supportNorm_union [DecidableEq P] (w : P → ℝ) {s t : Finset P} (h : Disjoint s t) :
    supportNorm w (s ∪ t) = supportNorm w s * supportNorm w t :=
  Finset.prod_union h

theorem supportNorm_one_le (w : P → ℝ) (hw : ∀ p, 1 ≤ w p) (r : Finset P) :
    1 ≤ supportNorm w r := Finset.one_le_prod₀ (fun p _ => hw p)

theorem support_card_log_le (w : P → ℝ) (hw : ∀ p, 2 ≤ w p) (r : Finset P) :
    (r.card : ℝ) * Real.log 2 ≤ Real.log (supportNorm w r) := by
  have hb : (2 : ℝ) ^ r.card ≤ supportNorm w r := by
    simpa [supportNorm] using
      (Finset.prod_le_prod₀ (s := r) (f := fun _ => (2 : ℝ)) (g := w)
        (fun _ _ => by norm_num) (fun p _ => hw p))
  have h := Real.log_le_log (by positivity) hb
  rwa [Real.log_pow] at h

def AnnularEnergyBound {ι κ : Type*} (rowNorm : ι → ℝ) (colNorm : κ → ℝ)
    (K : ι → κ → ℂ) (M N B : ℝ) : Prop :=
  ∀ (rows : Finset ι) (cols : Finset κ),
    (∀ r ∈ rows, M ≤ rowNorm r ∧ rowNorm r ≤ 2 * M) →
    (∀ c ∈ cols, colNorm c ≤ N) →
    IsEnergyBound rows cols K B

variable [DecidableEq P]

def AnnularTagPool (w : P → ℝ) (X M N : ℝ) (pool : Finset (Finset P)) : Prop :=
  pool.Nonempty ∧ (↑pool : Set (Finset P)).PairwiseDisjoint id ∧
    (∀ t ∈ pool, X ≤ supportNorm w t ∧ supportNorm w t ≤ (4 / 3) * X) ∧
    4 * Real.log (2 * (M * N)) ≤ (pool.card : ℝ) * Real.log 2

theorem isEnergyBound_narrow_annulus
    (w : P → ℝ) (hw : ∀ p, 2 ≤ w p) (K : Finset P → Finset P → ℂ)
    (hK : ∀ r c, ‖K r c‖ ≤ 1)
    (hmul : ∀ t r c, Disjoint t r → Disjoint t c → K (t ∪ r) c = K t c * K r c)
    (hunit : ∀ t c, Disjoint t c → ‖K t c‖ = 1)
    {x M N L B : ℝ} (hx : 0 < x) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hL : 0 < L) (hB : 0 ≤ B)
    (rows cols pool : Finset (Finset P))
    (hr : ∀ r ∈ rows, x ≤ supportNorm w r ∧ supportNorm w r ≤ (3 / 2) * x ∧
      supportNorm w r ≤ 2 * M)
    (hc : ∀ c ∈ cols, supportNorm w c ≤ N)
    (hpool : AnnularTagPool w (L / x) M N pool)
    (hlarge : AnnularEnergyBound (supportNorm w) (supportNorm w) K L N B) :
    IsEnergyBound rows cols K (8 * B) := by
  obtain ⟨hp, hd, hscale, hsize⟩ := hpool
  have hn (a : Finset P) (ha : supportNorm w a ≤ 2 * (M * N)) :
      (tagOverlapCount pool a : ℝ) ≤ (pool.card : ℝ) / 4 := by
    have h := support_card_log_le w hw a
    have hp' := supportNorm_one_le w (fun p => by linarith [hw p]) a
    have hl := h.trans (Real.log_le_log (by linarith : 0 < supportNorm w a) ha)
    have hcard : (a.card : ℝ) ≤ (pool.card : ℝ) / 4 := by
      apply (le_of_mul_le_mul_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
      linarith
    exact (Nat.cast_le.mpr (tagOverlapCount_le pool hd a)).trans hcard
  apply isEnergyBound_tag_average rows cols pool K hB hp (fun r _ c _ => hK r c) ?_
    (fun t _ r _ c _ => hmul t r c) (fun t _ c _ => hunit t c)
    (fun r h => hn r ((hr r h).2.2.trans (by nlinarith)))
    (fun c h => hn c ((hc c h).trans (by nlinarith)))
  intro t ht
  apply hlarge _ cols ?_ hc
  intro r hr'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr'
  obtain ⟨hu', hdis⟩ := Finset.mem_filter.mp hu
  obtain ⟨hut, huu, _⟩ := hr u hu'
  obtain ⟨hlt, hlu⟩ := hscale t ht
  rw [supportNorm_union w hdis]
  have hLo : (L / x) * x = L := div_mul_cancel₀ L hx.ne'
  have hHi : (4 / 3 * (L / x)) * (3 / 2 * x) = 2 * L := by
    calc
      _ = 2 * ((L / x) * x) := by ring
      _ = _ := by rw [hLo]
  refine ⟨?_, ?_⟩
  · exact hLo ▸ mul_le_mul hlt hut hx.le ((div_nonneg hL.le hx.le).trans hlt)
  · exact hHi ▸ mul_le_mul hlu huu
      (zero_le_one.trans (supportNorm_one_le w (fun p => by linarith [hw p]) u))
      (by positivity [hL])

theorem annularEnergyBound_compare
    (w : P → ℝ) (hw : ∀ p, 2 ≤ w p) (K : Finset P → Finset P → ℂ)
    (hK : ∀ r c, ‖K r c‖ ≤ 1)
    (hmul : ∀ t r c, Disjoint t r → Disjoint t c → K (t ∪ r) c = K t c * K r c)
    (hunit : ∀ t c, Disjoint t c → ‖K t c‖ = 1)
    {M N L B : ℝ} (hM : 1 ≤ M) (hN : 1 ≤ N) (hL : 0 < L) (hB : 0 ≤ B)
    (lo hi : Finset (Finset P))
    (hlo : AnnularTagPool w (L / M) M N lo)
    (hhi : AnnularTagPool w (L / ((3 / 2) * M)) M N hi)
    (hlarge : AnnularEnergyBound (supportNorm w) (supportNorm w) K L N B) :
    AnnularEnergyBound (supportNorm w) (supportNorm w) K M N (16 * B) := by
  classical
  intro rows cols hr hc a
  let inside : Finset P → Prop := fun r => supportNorm w r ≤ (3 / 2) * M
  let low := rows.filter inside
  let high := rows.filter (fun r => ¬ inside r)
  have hlow : IsEnergyBound low cols K (8 * B) :=
    isEnergyBound_narrow_annulus w hw K hK hmul hunit (by linarith : 0 < M) hM hN hL hB
      low cols lo
      (fun r h => ⟨(hr r (Finset.mem_filter.mp h).1).1,
        (Finset.mem_filter.mp h).2, (hr r (Finset.mem_filter.mp h).1).2⟩)
      hc hlo hlarge
  have hhigh : IsEnergyBound high cols K (8 * B) :=
    isEnergyBound_narrow_annulus w hw K hK hmul hunit (by linarith : 0 < (3 / 2) * M)
      hM hN hL hB high cols hi (fun r h => by
        obtain ⟨hr', hs⟩ := Finset.mem_filter.mp h
        have hb := (hr r hr').2
        exact ⟨(lt_of_not_ge hs).le, by linarith, hb⟩) hc hhi hlarge
  calc
    _ = finiteEnergy low cols K a + finiteEnergy high cols K a :=
      (Finset.sum_filter_add_sum_filter_not rows inside _).symm
    _ ≤ (8 * B) * coeffMass cols a + (8 * B) * coeffMass cols a :=
      add_le_add (hlow a) (hhigh a)
    _ = _ := by ring

end
end ArtinMatthews.QuadraticScale

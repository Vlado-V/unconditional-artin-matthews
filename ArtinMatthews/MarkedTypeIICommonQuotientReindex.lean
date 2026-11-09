module

public import ArtinMatthews.MarkedTypeIICommonQuotientCounts
public import ArtinMatthews.GiantMarkedBilinearFinite
public import ArtinMatthews.MarkedTypeIISharedLabelSupport


set_option backward.privateInPublic true
@[expose] public section

/-! Group the literal common-quotient collision by its two numeric labels.
Both endpoint coefficients and the finite quotient carrier survive the
reindexing. The dyadic support removes labels outside the original cutoff. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators ComplexConjugate

variable {J : Type*} [Fintype J]

def markedTypeIIDyadCoefficient (P : J → Finset ℕ) (η : ℝ → ℂ) (Y : ℝ)
    (α β : ℕ → ℂ) : MarkedTypeIIEndpoint → ℂ :=
  markedTypeIIEndpointCoeff (fun a => (markedMajorLabelMass P:ℂ) * η ((a:ℝ)/Y)) α β

private theorem markedTypeII_quotient_product_sum (M N H : Finset ℕ)
    (labelWeight α β : ℕ → ℂ) (a b : ℕ) :
    (∑ v ∈ M×ˢN, ∑ w ∈ M×ˢN, (labelWeight a * α v.1 * β v.2) *
        conj (labelWeight b * α w.1 * β w.2) *
        ∑ h ∈ H, if v.1*v.2 = 1+a*h ∧ w.1*w.2 = 1+b*h then (1:ℂ) else 0) =
      labelWeight a * conj (labelWeight b) *
        ∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β a h *
          conj (markedTypeIIQuotientCoefficient M N α β b h) := by
  simp_rw [mul_sum]
  simp_rw [sum_comm (s := M×ˢN) (t := H)]
  apply sum_congr rfl
  intro h _
  simp_rw [markedTypeIIQuotientCoefficient,markedTypeIIProductFiber,sum_filter,
    map_sum,apply_ite (conj : ℂ →+* ℂ),map_zero,sum_mul,mul_sum]
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro w _
  by_cases hv : v.1*v.2 = 1+a*h <;> by_cases hw : w.1*w.2 = 1+b*h
  all_goals simp [hv,hw,map_mul]
  ring

theorem markedTypeII_common_quotient_collision_reindex (P : J → Finset ℕ) (M N H : Finset ℕ)
    (labelWeight α β : ℕ → ℂ) :
    markedTypeIICollisionSum (giantMarkedEndpoints P M N) H (markedTypeIIEndpointCoeff labelWeight α β) =
      ∑ z ∈ (markedMajorLabelSet P×ˢmarkedMajorLabelSet P).filter (fun z => ¬ z.1.Coprime z.2),
        labelWeight z.1 * conj (labelWeight z.2) *
          ∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β z.1 h *
            conj (markedTypeIIQuotientCoefficient M N α β z.2 h) := by
  unfold markedTypeIICollisionSum
  simp only [giantMarkedEndpoints_sum,sum_filter,sum_product]
  apply sum_congr rfl
  intro a _
  simp_rw [sum_comm (s := N) (t := markedMajorLabelSet P)]
  rw [sum_comm (s := M) (t := markedMajorLabelSet P)]
  apply sum_congr rfl
  intro b _
  change (∑ m ∈ M, ∑ n ∈ N, ∑ r ∈ M, ∑ s ∈ N,
      if a.Coprime b then 0 else (labelWeight a * α m * β n) *
        conj (labelWeight b * α r * β s) *
        ∑ h ∈ H, if m*n = 1+a*h ∧ r*s = 1+b*h then (1:ℂ) else 0) =
      if ¬ a.Coprime b then labelWeight a * conj (labelWeight b) *
        ∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β a h *
          conj (markedTypeIIQuotientCoefficient M N α β b h) else 0
  by_cases hcop : a.Coprime b
  · simp [hcop]
  · simp only [hcop,ite_false,not_false_eq_true,ite_true]
    simpa only [sum_product] using markedTypeII_quotient_product_sum M N H labelWeight α β a b

theorem markedTypeII_dyad_collision_reindex (P : J → Finset ℕ) (M N H : Finset ℕ)
    (η : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (hη : Function.support η ⊆ Set.Icc 1 4)
    (α β : ℕ → ℂ) :
    markedTypeIICollisionSum (giantMarkedEndpoints P M N) H (markedTypeIIDyadCoefficient P η Y α β) =
      ∑ z ∈ (markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter
        (fun z => ¬ z.1.Coprime z.2),
        ((markedMajorLabelMass P:ℂ) * η ((z.1:ℝ)/Y)) *
          conj ((markedMajorLabelMass P:ℂ) * η ((z.2:ℝ)/Y)) *
          ∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β z.1 h *
            conj (markedTypeIIQuotientCoefficient M N α β z.2 h) := by
  rw [markedTypeIIDyadCoefficient,markedTypeII_common_quotient_collision_reindex]
  symm
  apply sum_subset
  · intro z hz
    obtain ⟨hbox,hcop⟩ := mem_filter.mp hz
    obtain ⟨ha,hb⟩ := mem_product.mp hbox
    exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_filter.mp ha).1,(mem_filter.mp hb).1⟩,hcop⟩
  · intro z hz hn
    obtain ⟨hbox,hcop⟩ := mem_filter.mp hz
    obtain ⟨ha,hb⟩ := mem_product.mp hbox
    have hdyad {a : ℕ} (ha : a ∈ markedMajorLabelSet P) (hn : η ((a:ℝ)/Y) ≠ 0) :
        a ∈ markedTypeIIDyadLabels P Y := by
      obtain ⟨hlo,hhi⟩ := hη hn
      refine mem_filter.mpr ⟨ha,?_,(div_le_iff₀ hY).mp hhi⟩
      simpa only [one_mul] using (le_div_iff₀ hY).mp hlo
    by_cases hzero : η ((z.1:ℝ)/Y) = 0
    · simp only [hzero,mul_zero,zero_mul]
    · have hzero' : η ((z.2:ℝ)/Y) = 0 := by
        by_contra h
        exact hn (mem_filter.mpr ⟨mem_product.mpr ⟨hdyad ha hzero,hdyad hb h⟩,hcop⟩)
      simp only [hzero',mul_zero,map_zero,zero_mul]

end
end ArtinMatthews

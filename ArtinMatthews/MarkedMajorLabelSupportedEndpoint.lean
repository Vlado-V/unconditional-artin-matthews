module

public import ArtinMatthews.MarkedMajorLabelEndpointConjugateIdentity


set_option backward.privateInPublic true
@[expose] public section

/-! Exact zero-weight removal puts the source endpoints in the fixed
positive compact interval required by the actual two-variable Mellin kernel. -/
namespace ArtinMatthews
open Finset

noncomputable def markedMajorSupportedTripleSet {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) (Y u v : ℝ) (l r : ℕ) : Finset (ℕ×(ℕ×ℕ)) := by
  classical
  exact (markedMajorLabelTripleSet bands u v l r).filter (fun z => cutoff ((z.1:ℝ)/Y) ≠ 0)

theorem markedMajorSupportedEndpoint_eq {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (w : ℕ×(ℕ×ℕ) → ℝ) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorSupportedTripleSet bands cutoff Y u v l r)
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β) w t =
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelTripleCoefficient bands cutoff χb θ Y χ W modulation β) w t := by
  classical
  unfold markedMajorEndpointPolynomial
  apply sum_subset (filter_subset _ _)
  intro z hz hznot
  have hz0 : cutoff ((z.1:ℝ)/Y)=0 := by
    by_contra h
    exact hznot (mem_filter.mpr ⟨hz,h⟩)
  simp only [markedMajorLabelTripleCoefficient,markedMajorLabelWeight,hz0,zero_mul]

theorem markedMajorSupportedConjugateEndpoint_eq {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {k q : ℕ}
    (χb : DirichletCharacter ℂ k) (θ Y : ℝ) (χ : DirichletCharacter ℂ q)
    (W modulation u v : ℝ) (l r : ℕ) (β : ℕ → ℂ)
    (w : ℕ×(ℕ×ℕ) → ℝ) (t : ℝ) :
    markedMajorEndpointPolynomial (markedMajorSupportedTripleSet bands cutoff Y u v l r)
      (markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β) w t =
    markedMajorEndpointPolynomial (markedMajorLabelTripleSet bands u v l r)
      (markedMajorLabelConjugateTripleCoefficient bands cutoff χb θ Y χ W modulation β) w t := by
  simp only [markedMajorLabelConjugateTripleCoefficient_eq]
  exact markedMajorSupportedEndpoint_eq bands cutoff χb θ Y χ W (-modulation) u v l r β w t

theorem markedMajorSupportedTriple_compact {J : Type*} [Fintype J]
    (bands : J → Finset ℕ) (cutoff : ℝ → ℂ) {lo hi Y H u v U : ℝ}
    (hlo : 0 < lo) (hsupp : Function.support cutoff ⊆ Set.Icc lo hi)
    (hY : 0 < Y) (hH : 0 < H) (hU : 0 < U)
    (hHu : H ≤ u) (huv : u ≤ v) (hvH : v ≤ 2*H)
    (l r : ℕ) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (z : ℕ×(ℕ×ℕ)) (hz : z ∈ markedMajorSupportedTripleSet bands cutoff Y u v l r) :
    markedMajorLabelTripleValue z/(Y*H*U) ∈ Set.Icc lo (4*hi) := by
  classical
  have hzmem := mem_filter.mp hz
  obtain ⟨_,hm,hn⟩ := by simpa only [markedMajorLabelTripleSet,mem_product] using hzmem.1
  have hlabel := hsupp hzmem.2
  have hslo : lo*Y ≤ (z.1:ℝ) := (le_div_iff₀ hY).mp hlabel.1
  have hshi : (z.1:ℝ) ≤ hi*Y := (div_le_iff₀ hY).mp hlabel.2
  have hhi : 0 < hi := hlo.trans_le (hlabel.1.trans hlabel.2)
  have hml : H ≤ (z.2.1:ℝ) := hHu.trans ((Nat.floor_lt (hH.le.trans hHu)).mp (mem_Ioc.mp hm).1).le
  have hmu : (z.2.1:ℝ) ≤ 2*H :=
    (show (z.2.1:ℝ) ≤ ⌊v⌋₊ by exact_mod_cast (mem_Ioc.mp hm).2).trans
      ((Nat.floor_le ((hH.le.trans hHu).trans huv)).trans hvH)
  have hnl : U ≤ (z.2.2:ℝ) := hl.trans (by exact_mod_cast (mem_Icc.mp hn).1)
  have hnu : (z.2.2:ℝ) ≤ 2*U := (show (z.2.2:ℝ) ≤ r by exact_mod_cast (mem_Icc.mp hn).2).trans hr
  have hsml := mul_le_mul hslo hml hH.le (Nat.cast_nonneg _)
  have hsmnl := mul_le_mul hsml hnl hU.le (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hsmu := mul_le_mul hshi hmu (Nat.cast_nonneg _) (mul_nonneg hhi.le hY.le)
  have hsmnu := mul_le_mul hsmu hnu (Nat.cast_nonneg _) (by positivity : 0 ≤ (hi*Y)*(2*H))
  unfold markedMajorLabelTripleValue
  rw [Nat.cast_mul,Nat.cast_mul]
  constructor
  · apply (le_div_iff₀ (mul_pos (mul_pos hY hH) hU)).mpr
    nlinarith only [hsmnl]
  · apply (div_le_iff₀ (mul_pos (mul_pos hY hH) hU)).mpr
    nlinarith only [hsmnu]

end ArtinMatthews

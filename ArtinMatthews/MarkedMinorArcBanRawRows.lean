module

public import ArtinMatthews.MarkedMinorArcBanRawColumn


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete finite raw-fiber rows, with the literal tilted collision mass. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

theorem markedBanRaw_collision_mass_eq {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (q x : ℝ) {M : ℕ}
    (source : MarkedRawActive (markedRawActualPrimeBand e x) M) :
    (∑ t : (j : J) → ↥(markedRawActualPrimeBand e x j),
      (if MarkedRawFullCrossBan source t then (1:ℝ) else 0)*
        markedRawLastMass (markedRawActualPrimeAtom e q x) t) =
      markedEventMass (markedFreshTiltedLaw e q x)
        (MarkedBanFreshCollision (markedBanRawNaturalActive e x source)) := by
  classical
  unfold markedEventMass
  rw [← Equiv.sum_comp (markedBanRawLastEquiv e x) (fun t =>
    (if MarkedBanFreshCollision (markedBanRawNaturalActive e x source) t then (1:ℝ) else 0)*
      markedFreshTiltedLaw e q x t)]
  apply Finset.sum_congr rfl
  intro t _
  rw [markedBanRawLastMass_eq,markedBanRawFullCrossBan_iff]

theorem markedRawBanMajorant_row_le_collision {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (μ : (j : J) → ↥(P j) → ℝ) (hμ : ∀ j p, 0 ≤ μ j p)
    (r : ℝ) (complement : Z → ℤ × ℤ)
    (hdet : ∀ z : Z, markedMinorIntegerDet z.1 (complement z)=1)
    (hz : ∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0)
    (hgeo : ∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16)
    (ψ : ℝ → ℂ) {Q Y A W : ℝ} (hQ : 1 ≤ Q) (hY : 1 ≤ Y)
    (hA : 0 ≤ A) (hW : 0 ≤ W) (hψ : ∀ t, ‖ψ t‖ ≤ W)
    (hsupp : ∀ t, ψ t ≠ 0 → |t| ≤ A)
    (bg : MarkedRawBackground P pads B) (u : MarkedRawCleanFiber P Z) :
    (∑ v : MarkedRawCleanFiber P Z,
      markedRawLastMass μ v.2*markedRawBanMajorant ψ Q Y bg u v) ≤
    (∑ t : (j : J) → ↥(P j),
      (if MarkedRawFullCrossBan (markedRawBanSourceActive bg u) t then (1:ℝ) else 0)*
        markedRawLastMass μ t)*((33*W*(8*A+5))*Q^3) := by
  classical
  let D : ℤ := markedRawCopiedProduct bg.1
  let V := Z.filter (fun v => D ∣ markedMinorIntegerDet u.1.1 v)
  have hlast (t : (j : J) → ↥(P j)) : 0 ≤ markedRawLastMass μ t :=
    Finset.prod_nonneg (fun j _ => hμ j (t j))
  have hkernel (t : (j : J) → ↥(P j)) :
      (∑ v ∈ V, ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ)
        (markedRawLastProduct t:ℤ) (markedBanNormalizedDet u.1.1 D v)‖) ≤
          (33*W*(8*A+5))*Q^3 := by
    have hh := markedBan_kernel_row_bound_polynomial r u.1.1 (complement u.1) D
      (markedRawLastProduct u.2:ℤ) (markedRawLastProduct t:ℤ) (hdet u.1) (hz u.1) V
      (fun v hv => ⟨(Finset.mem_filter.mp hv).2,hgeo u.1 ⟨v,(Finset.mem_filter.mp hv).1⟩⟩)
      ψ hQ hY hA hW hψ hsupp (fun _ => 1) (fun _ _ => by simp)
    simpa only [one_mul] using hh
  rw [Fintype.sum_prod_type,Finset.sum_comm,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro t _
  by_cases ht : MarkedRawFullCrossBan (markedRawBanSourceActive bg u) t
  · have he : (∑ v : Z, markedRawLastMass μ t*markedRawBanMajorant ψ Q Y bg u (v,t)) =
        markedRawLastMass μ t*∑ v ∈ V,
          ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ) (markedRawLastProduct t:ℤ)
            (markedBanNormalizedDet u.1.1 D v)‖ := by
      rw [← Finset.mul_sum]
      congr 1
      simp only [markedRawBanMajorant,markedBanRemovedCoefficient_norm,
        MarkedRawCleanBan,ht,ite_true]
      simpa only [V,Finset.sum_filter,D] using (Finset.sum_coe_sort Z (fun v =>
        if D ∣ markedMinorIntegerDet u.1.1 v then
          ‖markedBanEdgeKernel ψ Q Y (markedRawLastProduct u.2:ℤ) (markedRawLastProduct t:ℤ)
            (markedBanNormalizedDet u.1.1 D v)‖ else 0))
    rw [he,ite_eq_left ht,one_mul]
    exact mul_le_mul_of_nonneg_left (hkernel t) (hlast t)
  · simp only [ite_eq_right ht,zero_mul]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro v _
    simp only [markedRawBanMajorant,markedBanRemovedCoefficient_norm,MarkedRawCleanBan,
      ht,ite_false]
    split_ifs <;> simp

theorem markedRawBanMajorant_actual_row_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (pads B : ℕ) (Z : Finset (ℤ × ℤ)) (q r : ℝ)
      (complement : Z → ℤ × ℤ)
      (ψ : ℝ → ℂ) (Q Y A W : ℝ)
      (bg : MarkedRawBackground (markedRawActualPrimeBand e x) pads B)
      (u : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z),
      0 ≤ q → q ≤ 1 → (∀ z : Z, markedMinorIntegerDet z.1 (complement z)=1) →
      (∀ z : Z, markedMinorIntegerTau r z.1 ≠ 0) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      1 ≤ Q → 1 ≤ Y → 0 ≤ A → 0 ≤ W →
      (∀ t, ‖ψ t‖ ≤ W) → (∀ t, ψ t ≠ 0 → |t| ≤ A) →
      (∑ v : MarkedRawCleanFiber (markedRawActualPrimeBand e x) Z,
        markedRawLastMass (markedRawActualPrimeAtom e q x) v.2 *
          markedRawBanMajorant ψ Q Y bg u v) ≤
        markedBanErrorConstant (Fintype.card J) A W*(pads+1)*Q^3*
          Real.exp (-((Real.log x)^(1/10:ℝ))) := by
  classical
  filter_upwards [markedBan_actual_collision_mass_eventually e he hinj,
    marked_actual_tilted_atom_comparison_eventually e he] with x hc ha
  intro pads B Z q r complement ψ Q Y A W bg u hq0 hq1 hdet hz hgeo hQ hY hA hW hψ hsupp
  have hμ : ∀ j p, 0 ≤ markedRawActualPrimeAtom e q x j p := by
    intro j p
    rw [markedRawActualPrimeAtom_eq_tilted]
    exact (ha q hq0 hq1 j _).1
  apply (markedRawBanMajorant_row_le_collision (markedRawActualPrimeAtom e q x) hμ r
    complement hdet hz hgeo ψ hQ hY hA hW hψ hsupp bg u).trans
  rw [markedBanRaw_collision_mass_eq]
  have hm := mul_le_mul_of_nonneg_right
    (hc (pads+1) (markedBanRawNaturalActive e x (markedRawBanSourceActive bg u)) q hq0 hq1)
    (by positivity : 0 ≤ (33*W*(8*A+5))*Q^3)
  exact hm.trans_eq (by unfold markedBanErrorConstant; push_cast; ring)

end ArtinMatthews

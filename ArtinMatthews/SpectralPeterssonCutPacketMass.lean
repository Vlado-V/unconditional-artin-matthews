module

public import ArtinMatthews.SpectralPeterssonCutSeedInner
public import ArtinMatthews.SpectralPeterssonCutPacketPeriodization
public import ArtinMatthews.SpectralPeterssonPhysicalNorm


set_option backward.privateInPublic true
@[expose] public section

/-! Sharp-cut normalized packets have the exact incomplete-Gamma mass.
All off-diagonal frequency pairs vanish in the actual unit strip. -/
noncomputable section
open Set MeasureTheory UpperHalfPlane
open scoped ComplexConjugate BigOperators

namespace ArtinMatthews

variable {ι : Type*}

private theorem cutPacket_pair_expansion (k : ℕ) (t : Finset ι) (α : ι → ℂ)
    (n : ι → ℕ+) (A : ℝ) (z : UpperHalfPlane) :
    UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutPacket k t α n A)
      (spectralPeterssonStripCutPacket k t α n A) z =
      ∑ i ∈ t, ∑ j ∈ t,
        (conj (α i)*α j*((spectralPeterssonNormalization k (n i)*
          spectralPeterssonNormalization k (n j) : ℝ) : ℂ))*
          UpperHalfPlane.petersson (k : ℤ) (spectralPeterssonStripCutSeed (n i) A)
            (spectralPeterssonStripCutSeed (n j) A) z := by
  classical
  simp only [spectralPeterssonStripCutPacket_eq_sum,UpperHalfPlane.petersson,
    map_sum,map_mul,Complex.conj_ofReal,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

theorem spectralPeterssonStripCutPacket_pair_integrable (k : ℕ) (hk : 2 ≤ k)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ) :
    Integrable (fun z => UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutPacket k t α n A) (spectralPeterssonStripCutPacket k t α n A) z) := by
  have hi := integrable_finsetSum t (fun i hi => integrable_finsetSum t (fun j hj =>
    (spectralPeterssonStripCut_inner_integrable k hk (n i) (n j) A).const_mul
      (conj (α i)*α j*((spectralPeterssonNormalization k (n i)*spectralPeterssonNormalization k (n j) : ℝ) : ℂ))))
  exact Integrable.congr hi (Filter.Eventually.of_forall
    (fun z => (cutPacket_pair_expansion k t α n A z).symm))

theorem spectralPeterssonStripCutPacket_mass (k : ℕ) (hk : 2 ≤ k)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ) (hA : 0 ≤ A)
    (hn : Set.InjOn n (t : Set ι)) :
    (∫ z : UpperHalfPlane, ‖spectralPeterssonStripCutPacket k t α n A z‖^2*z.im^k) =
      spectralPeterssonGammaTailRatio k A*∑ i ∈ t, ‖α i‖^2 := by
  classical
  let P (z : UpperHalfPlane) := UpperHalfPlane.petersson (k : ℤ)
    (spectralPeterssonStripCutPacket k t α n A) (spectralPeterssonStripCutPacket k t α n A) z
  let B (i j : ι) : ℂ := conj (α i)*α j*((spectralPeterssonNormalization k (n i)*
    spectralPeterssonNormalization k (n j) : ℝ) : ℂ)
  have hij (i j : ι) : Integrable (fun z => B i j*UpperHalfPlane.petersson (k : ℤ)
      (spectralPeterssonStripCutSeed (n i) A) (spectralPeterssonStripCutSeed (n j) A) z) :=
    (spectralPeterssonStripCut_inner_integrable k hk (n i) (n j) A).const_mul _
  have hP : (∫ z, P z) = ∑ i ∈ t, ∑ j ∈ t,
      B i j*(if n i = n j then (spectralPeterssonTruncatedMass k (n j) A : ℂ) else 0) := by
    simp_rw [P,cutPacket_pair_expansion]
    rw [integral_finsetSum t (fun i hi => integrable_finsetSum t (fun j hj => hij i j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum t (fun j hj => hij i j)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_const_mul,spectralPeterssonStripCut_inner k hk (n i) (n j) A hA]
  have he : (∫ z, P z) =
      ((spectralPeterssonGammaTailRatio k A*∑ i ∈ t, ‖α i‖^2 : ℝ) : ℂ) := by
    rw [hP,Finset.mul_sum,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl,spectralPeterssonTruncatedMass_eq k hk]
      have hm : spectralPeterssonNormalization k (n i)*spectralPeterssonNormalization k (n i)*
          spectralPeterssonReproducingMass k (n i) = 1 := by
        simpa only [div_self (ne_of_gt (Real.sqrt_pos.mpr (spectralPeterssonReproducingMass_pos k hk (n i))))]
          using spectralPeterssonNormalization_mass k hk (n i) (n i)
      dsimp only [B]
      rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
      push_cast
      calc
        _ = (‖α i‖^2 : ℝ)*((spectralPeterssonNormalization k (n i)*
          spectralPeterssonNormalization k (n i)*spectralPeterssonReproducingMass k (n i) : ℝ) : ℂ)*
          (spectralPeterssonGammaTailRatio k A : ℂ) := by push_cast; ring
        _ = _ := by rw [hm]; push_cast; ring
    · intro j hj hji
      have hne : n i ≠ n j := fun h => hji (hn hi hj h).symm
      rw [if_neg hne,mul_zero]
    · intro hi'
      exact (hi' hi).elim
  have hreal : (∫ z, P z) =
      ((∫ z : UpperHalfPlane, ‖spectralPeterssonStripCutPacket k t α n A z‖^2*z.im^k : ℝ) : ℂ) := by
    simp only [P,spectralPetersson_self_pair,integral_complex_ofReal]
  exact Complex.ofReal_injective (hreal.symm.trans he)

theorem spectralPeterssonStripCutPacket_norm_integrable (k : ℕ) (hk : 2 ≤ k)
    (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+) (A : ℝ) :
    Integrable (fun z : UpperHalfPlane => ‖spectralPeterssonStripCutPacket k t α n A z‖^2*z.im^k) :=
  spectralPetersson_self_integrable k _ (spectralPeterssonStripCutPacket_pair_integrable k hk t α n A)

end ArtinMatthews

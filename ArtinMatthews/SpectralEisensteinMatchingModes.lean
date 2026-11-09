module

public import ArtinMatthews.SpectralEisensteinMatchingResponse
public import ArtinMatthews.SpectralEisensteinEquivalentMeans
public import ArtinMatthews.SpectralEisensteinScatteringContinuation


set_option backward.privateInPublic true
@[expose] public section

/-! The finite outgoing channels have exactly the independent actual cusp
tails required for matching. The continued original remainder has these
same tails with its already identified true scattering coefficients. -/
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0EisensteinCuspClassRepresentative_equivalent (N : ℕ) (r : SL(2,ℤ)) :
    gamma0EisensteinCuspsEquivalent N r
      (gamma0EisensteinCuspClassRepresentative N (gamma0EisensteinCuspClass N r)) := by
  apply (gamma0EisensteinCuspClass_eq_iff N _ _).mp
  rw [gamma0EisensteinCuspClassRepresentative_class]

theorem gamma0EisensteinMatchingForm_mem_iff (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    u∈(gamma0EisensteinMatchingForm N).subspace ↔
      ∀ i : Gamma0EisensteinCuspClasses N,
        gamma0CuspConstantTerm N (gamma0EisensteinCuspClassRepresentative N i)
          (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
          (gamma0EnergyInclusion N u)=0 := by
  let A := gamma0EisensteinMatchingHeight N
  let hA := gamma0EisensteinMatchingHeight_pos N
  change u∈gamma0TruncatedMeanZeroEnergy N A hA ↔ _
  rw [mem_gamma0TruncatedMeanZeroEnergy_iff]
  refine ⟨fun h i => h _,fun h r => ?_⟩
  rw [gamma0CuspConstantTerm_equivalent N r _
    (gamma0EisensteinCuspClassRepresentative_equivalent N r) A hA]
  exact h (gamma0EisensteinCuspClass N r)

theorem gamma0CuspOutgoingCutoffEnergy_sum_matching_mode (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (q : ℂ) (hq : q.re<1/2) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0CuspConstantTerm N r (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
      (gamma0EnergyInclusion N
        (∑ i, c i • gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i) q hq)) =
      c (gamma0EisensteinCuspClass N r) • gamma0CuspOutgoingTail N r q hq := by
  simp only [map_sum,map_smul,gamma0CuspOutgoingCutoffEnergy_mass,
    gamma0CuspOutgoingCutoffMass_matching_mode,smul_smul,gamma0CuspEisensteinIndicator_eq_cuspClass,
    gamma0EisensteinCuspClassRepresentative_class]
  rw [Finset.sum_eq_single (gamma0EisensteinCuspClass N r)]
  · simp
  · intro i _ hi
    simp only [ite_eq_right hi.symm,mul_zero,zero_smul]
  · simp

theorem gamma0CuspOutgoingCutoffEnergy_sum_mem_imp_zero (N : ℕ) [NeZero N]
    (q : ℂ) (hq : q.re<1/2) (c : Gamma0EisensteinCuspClasses N → ℂ)
    (hc : (∑ i, c i • gamma0CuspOutgoingCutoffEnergy N (gamma0EisensteinCuspClassRepresentative N i) q hq)
      ∈ (gamma0EisensteinMatchingForm N).subspace) : c=0 := by
  funext i
  have he := (gamma0EisensteinMatchingForm_mem_iff N _).mp hc i
  rw [gamma0CuspOutgoingCutoffEnergy_sum_matching_mode,
    gamma0EisensteinCuspClassRepresentative_class] at he
  exact (smul_eq_zero.mp he).resolve_right (gamma0CuspOutgoingTail_ne_zero N _ q hq)

theorem gamma0CuspOutgoingTail_equivalent (N : ℕ) [NeZero N] (r b : SL(2,ℤ))
    (h : gamma0EisensteinCuspsEquivalent N r b) (q : ℂ) (hq : q.re<1/2) :
    gamma0CuspOutgoingTail N r q hq=gamma0CuspOutgoingTail N b q hq := by
  apply Lp.ext
  filter_upwards [gamma0CuspOutgoingTail_ae N r q hq,gamma0CuspOutgoingTail_ae N b q hq]
    with y hr hb
  rw [hr,hb,gamma0EisensteinCuspsEquivalent_width N r b h]

theorem gamma0CuspEisensteinContinuedRemainder_matching_mode (N : ℕ) [NeZero N]
    (r a : SL(2,ℤ)) (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain)
    (hq : (1-s).re<1/2) :
    gamma0CuspConstantTerm N r (gamma0EisensteinMatchingHeight N) (gamma0EisensteinMatchingHeight_pos N)
      (gamma0CuspEisensteinContinuedRemainder N a s)=
      gamma0CuspScatteringContinued N r a s • gamma0CuspOutgoingTail N r (1-s) hq := by
  let A := gamma0EisensteinMatchingHeight N
  let hA := gamma0EisensteinMatchingHeight_pos N
  have hraw := ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi (gamma0EisensteinMatchingHeight_high N r))
    (gamma0CuspEisensteinContinuedRemainder_normalized_constant_mode N r a s hs)
  have hw : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hmode := (spectralCuspVerticalL2_ae_iff hw hA).mpr hraw
  have hconst := (gamma0GlobalCuspConstantTerm_ae N r (gamma0CuspEisensteinContinuedRemainder N a s)
    A hA).symm.trans hmode
  apply Lp.ext
  filter_upwards [hconst,gamma0CuspOutgoingTail_ae N r (1-s) hq,
    Lp.coeFn_smul (gamma0CuspScatteringContinued N r a s) (gamma0CuspOutgoingTail N r (1-s) hq)]
    with y hy ht hh
  rw [hy,hh,Pi.smul_apply,ht,smul_eq_mul]

theorem gamma0CuspScatteringContinued_equivalent_target (N : ℕ) [NeZero N]
    (r b a : SL(2,ℤ)) (he : gamma0EisensteinCuspsEquivalent N r b) (s : ℂ)
    (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0CuspScatteringContinued N r a s=gamma0CuspScatteringContinued N b a s := by
  have hq : (1-s).re<1/2 := by rw [Complex.sub_re,Complex.one_re];linarith [hs.1]
  have hr := gamma0CuspEisensteinContinuedRemainder_matching_mode N r a s hs hq
  have hb := gamma0CuspEisensteinContinuedRemainder_matching_mode N b a s hs hq
  rw [gamma0CuspConstantTerm_equivalent N r b he,
    gamma0CuspOutgoingTail_equivalent N r b he] at hr
  have hz : (gamma0CuspScatteringContinued N r a s-gamma0CuspScatteringContinued N b a s) •
      gamma0CuspOutgoingTail N b (1-s) hq=0 := by
    rw [sub_smul,← hr,← hb,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right (gamma0CuspOutgoingTail_ne_zero N b (1-s) hq))

end ArtinMatthews

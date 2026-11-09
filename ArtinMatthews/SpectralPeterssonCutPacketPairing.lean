module

public import ArtinMatthews.SpectralPeterssonCutSourcePairing
public import ArtinMatthews.SpectralPeterssonCutSourceL2
public import ArtinMatthews.SpectralPeterssonPhysicalPairing
public import ArtinMatthews.SpectralPeterssonSourcePackets


set_option backward.privateInPublic true
@[expose] public section

/-! The exact incomplete-Gamma factor for finite native source packets.
The target is any genuine cusp form, without a completeness hypothesis. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups ModularForm BigOperators ComplexConjugate

namespace ArtinMatthews

variable {ι : Type*}

theorem gamma0PeterssonCutPacket_infinity_pairing (N k : ℕ) [NeZero N]
    (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    (A : ℝ) (hA : 0 < A) (F : CuspForm (gamma0PeterssonRealGroup N) (k : ℤ)) :
    gamma0PeterssonInner N k (gamma0PeterssonCutPacket N 1 k t α n A) F =
      (spectralPeterssonGammaTailRatio k A : ℂ)*
        gamma0PeterssonInner N k (gamma0PeterssonSourceInfinityPacket N k t α n) F := by
  have hFLp := gamma0PeterssonCuspPacket_memLp N k F
  have hcut (j : ι) (_hj : j ∈ t) : IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ)
      (fun w => (spectralPeterssonNormalization k (n j) : ℂ)*gamma0PeterssonTruncatedPoincare N 1 k (n j) A w) F z)
      (gamma0InteriorRegion N) :=
    gamma0PeterssonPhysical_pair_integrable N k _ F
      (gamma0PeterssonCutSourceInfinity_memLp N k hk (n j) A hA) hFLp
  have hsource (j : ι) (_hj : j ∈ t) : IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ)
      (gamma0PeterssonSourceInfinity N k (n j)) F z) (gamma0InteriorRegion N) := by
    rw [← gamma0PeterssonSourceInfinityForm_coe N k hk hEven (n j)]
    exact gamma0PeterssonPhysical_pair_integrable N k _ F
      (gamma0PeterssonCuspPacket_memLp N k (gamma0PeterssonSourceInfinityForm N k hk hEven (n j))) hFLp
  have hform : gamma0PeterssonCutPacket N 1 k t α n A = fun z => ∑ j ∈ t, α j*
      ((spectralPeterssonNormalization k (n j) : ℂ)*gamma0PeterssonTruncatedPoincare N 1 k (n j) A z) := by
    funext z
    simp only [gamma0PeterssonCutPacket,mul_assoc]
  unfold gamma0PeterssonSourceInfinityPacket
  rw [hform,gamma0PeterssonInner_finset_left N k t α _ F hcut,
    gamma0PeterssonInner_finset_left N k t α _ F hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gamma0PeterssonCutSourceInfinity_pairing N k hk hEven (n j) A hA F]
  ring

theorem gamma0PeterssonCutPacket_mixed_pairing (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) {a b : ℤ} (hab : (r : ℤ)*a-(s : ℤ)*b=1)
    (k : ℕ) (hk : 2 ≤ k) (hEven : Even k) (t : Finset ι) (α : ι → ℂ) (n : ι → ℕ+)
    (A : ℝ) (hA : 0 < A) (F : CuspForm (gamma0PeterssonRealGroup (r*s)) (k : ℤ)) :
    gamma0PeterssonInner (r*s) k (gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A) F =
      (spectralPeterssonGammaTailRatio k A : ℂ)*
        gamma0PeterssonInner (r*s) k (gamma0PeterssonSourceAtkinPacket r s hab k t α n) F := by
  have hFLp := gamma0PeterssonCuspPacket_memLp (r*s) k F
  have hcut (j : ι) (_hj : j ∈ t) : IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ)
      (fun w => (spectralPeterssonNormalization k (n j) : ℂ)*
        gamma0PeterssonTruncatedPoincare (r*s) (gamma0CuspOneOver s) k (n j) A w) F z)
      (gamma0InteriorRegion (r*s)) :=
    gamma0PeterssonPhysical_pair_integrable (r*s) k _ F
      (gamma0PeterssonCutSourceAtkin_memLp r s hcop k hk (n j) A hA) hFLp
  have hsource (j : ι) (_hj : j ∈ t) : IntegrableOn (fun z => UpperHalfPlane.petersson (k : ℤ)
      (gamma0PeterssonSourceAtkin r s hab k (n j)) F z) (gamma0InteriorRegion (r*s)) := by
    rw [← gamma0PeterssonSourceAtkinForm_coe r s hcop hab k hk hEven (n j)]
    exact gamma0PeterssonPhysical_pair_integrable (r*s) k _ F
      (gamma0PeterssonCuspPacket_memLp (r*s) k (gamma0PeterssonSourceAtkinForm r s hcop hab k hk hEven (n j))) hFLp
  have hform : gamma0PeterssonCutPacket (r*s) (gamma0CuspOneOver s) k t α n A =
      fun z => ∑ j ∈ t, α j*((spectralPeterssonNormalization k (n j) : ℂ)*
        gamma0PeterssonTruncatedPoincare (r*s) (gamma0CuspOneOver s) k (n j) A z) := by
    funext z
    simp only [gamma0PeterssonCutPacket,mul_assoc]
  unfold gamma0PeterssonSourceAtkinPacket
  rw [hform,gamma0PeterssonInner_finset_left (r*s) k t α _ F hcut,
    gamma0PeterssonInner_finset_left (r*s) k t α _ F hsource,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [gamma0PeterssonCutSourceAtkin_pairing r s hcop hab k hk hEven (n j) A hA F]
  ring

end ArtinMatthews

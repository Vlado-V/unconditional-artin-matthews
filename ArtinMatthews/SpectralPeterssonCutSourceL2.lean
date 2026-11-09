module

public import ArtinMatthews.SpectralPeterssonCutPacketNorm
public import ArtinMatthews.SpectralPeterssonPhysicalCauchy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual normalized single cut vectors belong to the native
Petersson L2 space at infinity and at every exact-divisor cusp. -/
noncomputable section
open Set Matrix MeasureTheory UpperHalfPlane
open scoped MatrixGroups

namespace ArtinMatthews

private theorem cutPacket_unit_eq (N k : ℕ) [NeZero N] (a : SL(2, ℤ))
    (n : ℕ+) (A : ℝ) :
    gamma0PeterssonCutPacket N a k (Finset.univ : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => n) A =
      fun z => (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N a k n A z := by
  funext z
  simp [gamma0PeterssonCutPacket]

theorem gamma0PeterssonCutSourceInfinity_memLp (N k : ℕ) [NeZero N] (hk : 2 ≤ k)
    (n : ℕ+) (A : ℝ) (hA : 0 < A) :
    MemLp (spectralPeterssonHilbertProfile k (fun z =>
      (spectralPeterssonNormalization k n : ℂ)*gamma0PeterssonTruncatedPoincare N 1 k n A z)) 2
      (volume.restrict (gamma0InteriorRegion N)) := by
  have hinj : Set.InjOn (fun _ : Unit => n) ((Finset.univ : Finset Unit) : Set Unit) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have hI := (gamma0PeterssonCutPacket_infinity_norm N k hk (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA (show 0 < (n : ℝ) by positivity) hinj (fun _ _ => le_rfl)).1
  have hm := gamma0PeterssonCutPacket_measurable N 1 k (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA
  apply spectralPeterssonHilbertProfile_memLp_of_integrable N k _
  · simpa only [cutPacket_unit_eq] using hm
  · simpa [gamma0PeterssonCutPacket] using! hI

theorem gamma0PeterssonCutSourceAtkin_memLp (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (k : ℕ) (hk : 2 ≤ k) (n : ℕ+) (A : ℝ) (hA : 0 < A) :
    MemLp (spectralPeterssonHilbertProfile k (fun z =>
      (spectralPeterssonNormalization k n : ℂ)*
        gamma0PeterssonTruncatedPoincare (r*s) (gamma0CuspOneOver s) k n A z)) 2
      (volume.restrict (gamma0InteriorRegion (r*s))) := by
  have hinj : Set.InjOn (fun _ : Unit => n) ((Finset.univ : Finset Unit) : Set Unit) :=
    fun _ _ _ _ _ => Subsingleton.elim _ _
  have hI := (gamma0PeterssonCutPacket_mixed_norm r s hcop k hk (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA (show 0 < (n : ℝ) by positivity) hinj (fun _ _ => le_rfl)).1
  have hm := gamma0PeterssonCutPacket_measurable (r*s) (gamma0CuspOneOver s) k (Finset.univ : Finset Unit)
    (fun _ => (1 : ℂ)) (fun _ => n) hA
  apply spectralPeterssonHilbertProfile_memLp_of_integrable (r*s) k _
  · simpa only [cutPacket_unit_eq] using hm
  · simpa [gamma0PeterssonCutPacket] using! hI

end ArtinMatthews

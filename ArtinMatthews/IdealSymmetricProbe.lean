module

public import ArtinMatthews.IdealProbeProjection
public import ArtinMatthews.IdealProbeDecay


set_option backward.privateInPublic true
@[expose] public section

/-! Basis-free harmonic-product survivor bounds, with all dimension and
block-size parameters explicit. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealProbeProjection_harmonic_bound {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p)
    (probes tail : Finset (J × Fin M)) (groupProbes groupTail : J → Finset (Fin M)) (G : Finset J)
    (hp : ∀ j∈G,∀ i∈groupProbes j,(j,i)∈probes)
    (ht : ∀ j∈G,∀ i∈groupTail j,(j,i)∈tail)
    (hPT : ∀ j∈G,Disjoint (groupProbes j) (groupTail j)) (hM : 0 < M)
    (hm : ∀ j∈G,1 ≤ (groupProbes j).card) (hell : ∀ j∈G,1 ≤ (groupTail j).card)
    (hlarge : ∀ j∈G,((groupProbes j).card+(groupTail j).card)*
      ((groupProbes j).card+(groupTail j).card-1) ≤ M)
    (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    idealLabelEnergy P M (idealProbeProjection P probes tail f) ≤
      (∏ j∈G,((2:ℝ)/((groupProbes j).card+1 : ℕ)))*idealLabelEnergy P M f := by
  have hN (j : J) : Nonempty ↥(P j) := by
    by_contra h
    have he : P j=∅ := eq_empty_iff_forall_notMem.mpr fun p hp => h ⟨⟨p,hp⟩⟩
    have hv := hV j
    simp only [he,bandReciprocalMass,sum_empty] at hv
    exact (lt_irrefl 0 hv)
  let a₀ : ∀ j,↥(P j) := fun j => Classical.choice (hN j)
  have hw (j : J) (p : ↥(P j)) : 0 < markedHarmonicAtom (P j) p :=
    idealHarmonicAtom_pos (P j) (hV j) (hP j) p
  choose b hb using fun j => idealCoordinateBasis_exists (markedHarmonicAtom (P j))
    (fun p => (hw j p).le) (markedHarmonicAtom_sum (P j) (hV j)) (a₀ j)
  exact idealProbeProjection_symmetric_bound P hV hw b a₀ hb probes tail groupProbes groupTail G
    hp ht hPT hM hm hell hlarge f hf

theorem idealProbeProjection_uniform_bound {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {M m ell : ℕ} (hV : ∀ j,0 < bandReciprocalMass (P j))
    (hP : ∀ j p,p∈P j → 0 < p)
    (probes tail : Finset (J × Fin M)) (groupProbes groupTail : J → Finset (Fin M)) (G : Finset J)
    (hp : ∀ j∈G,∀ i∈groupProbes j,(j,i)∈probes)
    (ht : ∀ j∈G,∀ i∈groupTail j,(j,i)∈tail)
    (hPT : ∀ j∈G,Disjoint (groupProbes j) (groupTail j)) (hM : 0 < M)
    (hm : 1 ≤ m) (hell : 1 ≤ ell)
    (hpCard : ∀ j∈G,(groupProbes j).card=m) (htCard : ∀ j∈G,(groupTail j).card=ell)
    (hlarge : (m+ell)*(m+ell-1) ≤ M)
    (f : MarkedPhysicalMarking P M → ℂ) (hf : IdealSymmetric f) :
    idealLabelEnergy P M (idealProbeProjection P probes tail f) ≤
      ((2:ℝ)/(m+1 : ℕ))^G.card*idealLabelEnergy P M f := by
  have hbound := idealProbeProjection_harmonic_bound P hV hP probes tail groupProbes groupTail G
    hp ht hPT hM (fun j hj => (hpCard j hj).symm ▸ hm)
    (fun j hj => (htCard j hj).symm ▸ hell)
    (fun j hj => by rw [hpCard j hj,htCard j hj]; exact hlarge) f hf
  have he : (∏ j∈G,((2:ℝ)/((groupProbes j).card+1 : ℕ)))=((2:ℝ)/(m+1 : ℕ))^G.card := by
    calc
      _ = ∏ _j∈G,((2:ℝ)/(m+1 : ℕ)) := prod_congr rfl fun j hj => by rw [hpCard j hj]
      _ = _ := prod_const _
  simpa only [he] using hbound

end
end ArtinMatthews

module

public import ArtinMatthews.MarkedPhysicalPadLiftBox


set_option backward.privateInPublic true
@[expose] public section

/-! Literal four-coefficient scalar kernel and its actual support.
On a surviving copied-pad edge, nonzero scalar weights lift to two
valid primitive positions in the performed box. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable

def markedPhysicalScalarCofactorTerm (η : ℝ → ℂ) (Y : ℝ)
    (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
    (b a : ℕ) (v u : ℕ × ℕ) : ℂ :=
  η ((b:ℝ)/Y)*η ((a:ℝ)/Y)*detector b a ((b:ℤ)*v.1*u.2-(a:ℤ)*u.1*v.2)*
    (α v.1*conj (α u.1)*β u.2*conj (β v.2))

def MarkedPhysicalRoughAt (W : ℝ) (n : ℕ) : Prop :=
  ∀ p : ℕ,p.Prime → p ∣ n → W ≤ (p:ℝ)

theorem markedPhysicalRoughAt_of_avoids {W : ℝ} (hW : 0 ≤ W) {n : ℕ}
    (hn : ∀ p ∈ Nat.primesLE ⌊W⌋₊,¬p ∣ n) : MarkedPhysicalRoughAt W n := by
  intro p hp hpd
  by_contra hh
  have h := (Nat.le_floor_iff hW).mpr (lt_of_not_ge hh).le
  exact hn p (Nat.mem_primesLE.mpr ⟨h,hp⟩) hpd

theorem markedPhysicalScalarCofactorTerm_nonzero {η : ℝ → ℂ} {Y : ℝ}
    {detector : ℤ → ℤ → ℤ → ℂ} {α β : ℕ → ℂ} {b a : ℕ} {v u : ℕ × ℕ}
    (h : markedPhysicalScalarCofactorTerm η Y detector α β b a v u ≠ 0) :
    η ((b:ℝ)/Y) ≠ 0 ∧ η ((a:ℝ)/Y) ≠ 0 ∧
      detector b a ((b:ℤ)*v.1*u.2-(a:ℤ)*u.1*v.2) ≠ 0 ∧
      α v.1 ≠ 0 ∧ α u.1 ≠ 0 ∧ β v.2 ≠ 0 ∧ β u.2 ≠ 0 := by
  unfold markedPhysicalScalarCofactorTerm at h
  obtain ⟨⟨⟨hb,ha⟩,ht⟩,⟨⟨⟨hm,hr⟩,hn⟩,hs⟩⟩ := by
    simpa only [mul_ne_zero_iff] using h
  exact ⟨hb,ha,ht,hm,fun h0 => hr (by simp [h0]),fun h0 => hs (by simp [h0]),hn⟩

theorem markedPhysicalPadCofactorTerm_eq_scalar
    {J : Type*} [Fintype J] {P : J → Finset ℕ} {pads : ℕ}
    (η : ℝ → ℂ) (Y : ℝ) (detector : ℤ → ℤ → ℤ → ℂ) (α β : ℕ → ℂ)
    (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))
    (hban : ¬MarkedPhysicalCrossBan ((markedPhysicalMarkingSplit pads).symm (c,b)) a)
    (hα : ∀ m,α m ≠ 0 → MarkedPhysicalBandRough P m) (v u : ℕ × ℕ) :
    markedPhysicalPadCofactorTerm P pads η Y detector α β c b a v u =
      markedPhysicalScalarCofactorTerm η Y detector α β
        (markedPrimeBandProduct P b) (markedPrimeBandProduct P a) v u := by
  unfold markedPhysicalPadCofactorTerm markedPhysicalScalarCofactorTerm
  rw [ite_eq_right hban]
  by_cases h : MarkedPhysicalBandRough P v.1 ∧ MarkedPhysicalBandRough P u.1
  · rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    by_cases hm : α v.1=0
    · simp [hm]
    · have hr : α u.1=0 := by
        by_contra hne
        exact h ⟨hα _ hm,hα _ hne⟩
      simp [hr]

theorem markedPhysical_cutoff_label_range {η : ℝ → ℂ}
    (hη : Function.support η ⊆ Set.Icc 1 4) {Y : ℝ} (hY : 0 < Y)
    {b : ℕ} (hb : η ((b:ℝ)/Y) ≠ 0) : Y ≤ (b:ℝ) ∧ (b:ℝ) ≤ 4*Y := by
  have h := hη hb
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ hY).mp h.1,(div_le_iff₀ hY).mp h.2⟩

theorem markedPhysical_delta_major_small_support (ψ : ℝ → ℂ)
    {Y R W : ℝ} (hY : 0 < Y) (hψ : Function.support ψ ⊆ Set.Icc (-R) R) (hRW : R*Y < W)
    (Q : ℝ) :
    (∀ b a t : ℤ,markedRawEdgeDeltaDetector ψ Y b a t ≠ 0 → |(t:ℝ)| < W) ∧
      (∀ b a t : ℤ,markedRawEdgeMajorDetector ψ Q Y b a t ≠ 0 → |(t:ℝ)| < W) := by
  have h (t : ℤ) (ht : ψ ((t:ℝ)/Y) ≠ 0) : |(t:ℝ)| < W := by
    have habs := abs_le.mpr (hψ ht)
    rw [abs_div,abs_of_pos hY] at habs
    exact ((div_le_iff₀ hY).mp habs).trans_lt hRW
  exact ⟨fun _ _ t ht => h t (mul_ne_zero_iff.mp ht).1,
    fun _ _ t ht => h t (mul_ne_zero_iff.mp ht).1⟩

variable {J : Type*} [Fintype J] [Nonempty J] {P : J → Finset ℕ}
  (hP : ∀ j p,p ∈ P j → p.Prime)
  (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
  {pads : ℕ} (c : MarkedPhysicalMarking P pads) (b a : (j : J) → ↥(P j))
  {d₀ Y Hm Hn W : ℝ} (hd₀ : 0 ≤ d₀) (hY : 0 < Y) (hm₀ : 0 ≤ Hm)
  (hD : d₀ ≤ (markedPhysicalMarkingProduct c:ℝ) ∧ (markedPhysicalMarkingProduct c:ℝ) < 2*d₀)
  (hbelow : ∀ j p,p ∈ P j → (p:ℝ)<W)
  (hgood : ∀ j,¬MarkedPadCollision {b j,a j} (c j)) (hne : ∀ j,b j ≠ a j)
  {η : ℝ → ℂ} (hη : Function.support η ⊆ Set.Icc 1 4)
  {detector : ℤ → ℤ → ℤ → ℂ} (ht : ∀ b a t : ℤ,detector b a t ≠ 0 → |(t:ℝ)| < W)
  {α β : ℕ → ℂ} (S T : Finset ℕ)
  (hS : ∀ m∈S,Hm ≤ (m:ℝ) ∧ (m:ℝ) ≤ 2*Hm)
  (hT : ∀ n∈T,Hn ≤ (n:ℝ) ∧ (n:ℝ) ≤ 2*Hn)
  (hα : ∀ m,α m ≠ 0 → m ∈ S ∧ MarkedPhysicalRoughAt W m)
  (hβ : ∀ n,β n ≠ 0 → n ∈ T ∧ MarkedPhysicalRoughAt W n)

include hP hdis hd₀ hY hm₀ hD hbelow hgood hne hη ht hS hT hα hβ

theorem markedPhysicalScalarCofactorTerm_supported_lifts {v u : ℕ × ℕ}
    (hF : markedPhysicalScalarCofactorTerm η Y detector α β
      (markedPrimeBandProduct P b) (markedPrimeBandProduct P a) v u ≠ 0) :
    v ∈ S.product T ∧ u ∈ S.product T ∧
      (∃ v' : MarkedPhysicalCofactorCoordinates (Z := markedPhysicalPadBox d₀ Y Hm Hn)
        ((markedPhysicalMarkingSplit pads).symm (c,b)),v'.1=v) ∧
      (∃ u' : MarkedPhysicalCofactorCoordinates (Z := markedPhysicalPadBox d₀ Y Hm Hn)
        ((markedPhysicalMarkingSplit pads).symm (c,a)),u'.1=u) := by
  obtain ⟨hb,ha,hdet,hm,hr,hs,hn⟩ := markedPhysicalScalarCofactorTerm_nonzero hF
  obtain ⟨hms,hmR⟩ := hα _ hm
  obtain ⟨hrs,hrR⟩ := hα _ hr
  obtain ⟨hst,hsR⟩ := hβ _ hs
  obtain ⟨hnt,hnR⟩ := hβ _ hn
  refine ⟨Finset.mem_product.mpr ⟨hms,hst⟩,Finset.mem_product.mpr ⟨hrs,hnt⟩,?_⟩
  exact markedPhysicalPad_cofactor_lifts hP hdis c b a hd₀ hY.le hm₀ hD
    (markedPhysical_cutoff_label_range hη hY hb) (markedPhysical_cutoff_label_range hη hY ha)
    hbelow hgood hne (hS _ hms) (hS _ hrs) (hT _ hst) (hT _ hnt)
    (markedPhysicalBandRough_of_rough P hP hbelow hmR)
    (markedPhysicalBandRough_of_rough P hP hbelow hrR) hsR hnR
    (by exact_mod_cast ht _ _ _ hdet)

end
end ArtinMatthews

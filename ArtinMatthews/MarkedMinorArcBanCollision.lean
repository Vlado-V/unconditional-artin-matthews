module

public import ArtinMatthews.MarkedMinorArcDirtyFreshGood


set_option backward.privateInPublic true
@[expose] public section

/-! The actual probability cost of a fresh last slot hitting the full source list. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedBanSourceValues {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (source : (j : J) → Fin M → ↥(P j)) (j : J) : Finset ↥(P j) :=
  Finset.univ.image (source j)

theorem markedBanSourceValues_card_le {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (source : (j : J) → Fin M → ↥(P j)) (j : J) : (markedBanSourceValues source j).card ≤ M := by
  exact Finset.card_image_le.trans_eq (by simp)

def MarkedBanFreshCollision {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (source : (j : J) → Fin M → ↥(P j)) (fresh : (j : J) → ↥(P j)) : Prop :=
  ∃ i j k, (fresh i:ℕ) = (source j k:ℕ)

theorem markedBanFreshCollision_iff {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (hd : Pairwise (fun i j => Disjoint (P i) (P j)))
    (source : (j : J) → Fin M → ↥(P j)) (fresh : (j : J) → ↥(P j)) :
    MarkedBanFreshCollision source fresh ↔ ∃ j, fresh j ∈ markedBanSourceValues source j := by
  constructor
  · rintro ⟨i,j,k,he⟩
    have hij : i = j := by
      by_contra hn
      exact Finset.disjoint_left.mp (hd hn) (fresh i).2 (he.symm ▸ (source j k).2)
    subst j
    exact ⟨i,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,Subtype.ext he.symm⟩⟩
  · rintro ⟨j,hj⟩
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hj
    exact ⟨j,j,k,congrArg Subtype.val hk.symm⟩

theorem markedBan_coordinate_eventMass {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (μ : ∀ j, Ω j → ℝ)
    (hsum : ∀ j, ∑ p, μ j p = 1) (F : ∀ j, Finset (Ω j)) (i : J) :
    markedEventMass (finiteProductMass μ) (fun t => t i ∈ F i) = ∑ p ∈ F i, μ i p := by
  classical
  have hh := finiteProduct_expectation_coordinate μ (fun j p => if p ∈ F j then (1:ℝ) else 0) hsum i
  simpa only [markedEventMass,ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter] using hh

theorem markedBan_fresh_hits_mass_le {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (μ : ∀ j, Ω j → ℝ)
    (hμ : ∀ j p, 0 ≤ μ j p) (hsum : ∀ j, ∑ p, μ j p = 1)
    (F : ∀ j, Finset (Ω j)) {M : ℕ} (hF : ∀ j, (F j).card ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) (hatom : ∀ j p, μ j p ≤ δ) :
    markedEventMass (finiteProductMass μ) (fun t => ∃ j, t j ∈ F j) ≤
      (Fintype.card J:ℝ)*M*δ := by
  classical
  apply (markedEventMass_exists_le (finiteProductMass μ)
    (fun t => show 0 ≤ finiteProductMass μ t from Finset.prod_nonneg (fun j _ => hμ j (t j)))
    (fun j (t : ∀ j, Ω j) => t j ∈ F j)).trans
  calc
    _ = ∑ j, ∑ p ∈ F j, μ j p := by simp_rw [markedBan_coordinate_eventMass μ hsum F]
    _ ≤ ∑ _j : J, (M:ℝ)*δ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ∑ _p ∈ F j, δ := Finset.sum_le_sum (fun p _ => hatom j p)
        _ = ((F j).card:ℝ)*δ := by simp
        _ ≤ (M:ℝ)*δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hF j)) hδ
    _ = _ := by simp [mul_assoc]

theorem markedBan_actual_harmonic_atom_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ j,
      0 < bandReciprocalMass (markedLogPowerBand (e j) x) ∧
      ∀ p : ↥(markedLogPowerBand (e j) x),
        markedHarmonicAtom (markedLogPowerBand (e j) x) p ≤
          (2/Real.log 2)*Real.exp (-((Real.log x)^(1/10:ℝ))) := by
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j,
      Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually
      (show 0 < e j by linarith [he j])).mono (fun _ hx => hx.1.le))
  filter_upwards [hV,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hV hlog
  intro j
  have hVp := (by positivity : 0 < Real.log 2/2).trans_le (hV j)
  refine ⟨hVp,fun p => ?_⟩
  calc
    _ ≤ 1/(Real.exp ((Real.log x)^(1/10:ℝ))*bandReciprocalMass (markedLogPowerBand (e j) x)) :=
      markedHarmonicAtom_le _ hVp (Real.exp_pos _) (fun p hp => marked_band_common_lower (he j) hlog hp) p
    _ ≤ 1/(Real.exp ((Real.log x)^(1/10:ℝ))*(Real.log 2/2)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (hV j) (Real.exp_pos _).le)
    _ = _ := by rw [Real.exp_neg]; field_simp

theorem markedBan_actual_tilted_atom_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ j,
      ∀ p : ↥(markedLogPowerBand (e j) x),
        markedTiltedBandAtom (markedLogPowerBand (e j) x) q (markedMemoryMomentLength x) p ≤
          (4/Real.log 2)*Real.exp (-((Real.log x)^(1/10:ℝ))) := by
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he,
    markedBan_actual_harmonic_atom_eventually e he] with x ht hh
  intro q hq0 hq1 j p
  calc
    _ ≤ 2*markedHarmonicAtom (markedLogPowerBand (e j) x) p := (ht q hq0 hq1 j p).2
    _ ≤ 2*((2/Real.log 2)*Real.exp (-((Real.log x)^(1/10:ℝ)))) :=
      mul_le_mul_of_nonneg_left ((hh j).2 p) (by norm_num)
    _ = _ := by ring

theorem markedBan_actual_collision_mass_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (M : ℕ)
      (source : (j : J) → Fin M → ↥(markedLogPowerBand (e j) x)) (q : ℝ),
      0 ≤ q → q ≤ 1 →
      markedEventMass (markedFreshTiltedLaw e q x) (MarkedBanFreshCollision source) ≤
        (2:ℝ)^(Fintype.card J)*(Fintype.card J:ℝ)*M*
          ((2/Real.log 2)*Real.exp (-((Real.log x)^(1/10:ℝ)))) := by
  classical
  filter_upwards [marked_actual_tilted_atom_comparison_eventually e he,
    markedBan_actual_harmonic_atom_eventually e he,marked_array_disjoint_eventually e hinj]
      with x ht hh hd
  intro M source q hq0 hq1
  have hc := marked_fresh_event_mass_comparison _ _
    (fun j p => (ht q hq0 hq1 j p).1) (fun j p => (ht q hq0 hq1 j p).2)
    (MarkedBanFreshCollision source)
  have hμ := markedBan_fresh_hits_mass_le
    (fun j => markedHarmonicAtom (markedLogPowerBand (e j) x))
    (fun j _ => markedHarmonicAtom_nonneg _ (hh j).1)
    (fun j => markedHarmonicAtom_sum _ (hh j).1) (markedBanSourceValues source)
    (markedBanSourceValues_card_le source) (by positivity) (fun j p => (hh j).2 p)
  have hE : MarkedBanFreshCollision source =
      (fun fresh => ∃ j, fresh j ∈ markedBanSourceValues source j) := by
    funext fresh
    exact propext (markedBanFreshCollision_iff hd source fresh)
  rw [← hE] at hμ
  exact hc.trans (by
    have hm := mul_le_mul_of_nonneg_left hμ (by positivity : 0 ≤ (2:ℝ)^(Fintype.card J))
    simpa only [markedFreshTiltedLaw,markedFreshHarmonicLaw,mul_assoc] using hm)

end ArtinMatthews

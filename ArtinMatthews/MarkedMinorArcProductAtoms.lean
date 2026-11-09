module

public import ArtinMatthews.MarkedMinorArcProductMassActual
public import ArtinMatthews.MarkedMinorArcPrimeProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Literal pushed product atoms and the actual PD04 endpoint mass bound. -/
noncomputable section
namespace ArtinMatthews

open Filter
open scoped BigOperators Topology

def markedMemoryProductAtom {J : Type*} [Fintype J] (P : J → Finset ℕ)
    (V : J → ℝ) (q : ℝ) (N b : ℕ) : ℝ := by
  classical
  exact ∑ t : (j : J) → ↥(P j), if markedPrimeBandProduct P t = b then
    markedMemoryProductMass V q N (fun j => (t j:ℕ)) else 0

theorem markedMemoryProductAtom_nonneg {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (q : ℝ) (N b : ℕ)
    (hV : ∀ j, 0 < V j) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlarge : ∀ j p, p ∈ P j → 2*(N+1) ≤ p+1) :
    0 ≤ markedMemoryProductAtom P V q N b := by
  classical
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · exact Finset.prod_nonneg (fun j _ =>
      (markedMemoryPrimeAtom_pos (hV j) hq0 hq1 (hlarge j _ (t j).property)).le)
  · exact le_rfl

theorem markedMemoryProductAtom_at_product {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hprime : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (V : J → ℝ) (q : ℝ) (N : ℕ) (t : (j : J) → ↥(P j)) :
    markedMemoryProductAtom P V q N (markedPrimeBandProduct P t) =
      markedMemoryProductMass V q N (fun j => (t j:ℕ)) := by
  classical
  exact markedPrimeBandProduct_fiber_mass P hprime hdis _ t

theorem markedMemoryProductAtom_eq_zero_of_unrepresented {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (q : ℝ) (N b : ℕ)
    (hb : ¬∃ t, markedPrimeBandProduct P t = b) : markedMemoryProductAtom P V q N b = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro t _
  simp only [show markedPrimeBandProduct P t ≠ b from fun ht => hb ⟨t,ht⟩, ite_false]

def markedActualMemoryProductAtom {J : Type*} [Fintype J] (e : J → ℝ)
    (q x : ℝ) (b : ℕ) : ℝ :=
  markedMemoryProductAtom (fun j => markedLogPowerBand (e j) x)
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) q (markedMemoryMomentLength x) b

theorem marked_actual_memory_product_atom_nonneg_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ) (b : ℕ),
      0 ≤ q → q ≤ 1 → 0 ≤ markedActualMemoryProductAtom e q x b := by
  have hV : ∀ᶠ x : ℝ in atTop, ∀ j,
      Real.log 2/2 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    eventually_all.mpr (fun j => (marked_log_power_band_mass_eventually
      (show 0 < e j by linarith [he j])).mono (fun _ hx => hx.1.le))
  filter_upwards [hV, markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hV hN hlog
  intro q b hq0 hq1
  exact markedMemoryProductAtom_nonneg _ _ q _ b
    (fun j => (by positivity : 0 < Real.log 2/2).trans_le (hV j)) hq0 hq1
    (fun j p hp => hN p (marked_band_common_lower (he j) hlog hp))

/-- The actual pushed measure of every integer product in the source dyadic
support is bounded by C_K/Y, including unsupported products whose mass is zero. -/
theorem marked_actual_memory_product_atom_cutoff_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (b : ℕ),
      0 ≤ q → q ≤ 1 → 0 < Y → η ((b:ℝ)/Y) ≠ 0 →
      markedActualMemoryProductAtom e q x b ≤ (4/Real.log 2)^(Fintype.card J)/Y := by
  classical
  filter_upwards [marked_actual_memory_product_mass_cutoff_eventually e he η hη,
    marked_array_disjoint_eventually e hinj] with x hm hd
  intro q Y b hq0 hq1 hY hcut
  by_cases hb : ∃ t : (j : J) → ↥(markedLogPowerBand (e j) x),
      markedPrimeBandProduct (fun j => markedLogPowerBand (e j) x) t = b
  · obtain ⟨t,ht⟩ := hb
    unfold markedActualMemoryProductAtom
    rw [← ht, markedMemoryProductAtom_at_product _
      (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hd]
    have hcut' : η (((∏ j, (t j:ℕ):ℕ):ℝ)/Y) ≠ 0 := by
      change η ((markedPrimeBandProduct _ t:ℝ)/Y) ≠ 0
      rw [ht]
      exact hcut
    exact hm q Y (fun j => (t j:ℕ)) hq0 hq1 hY (fun j => (t j).property) hcut'
  · rw [markedActualMemoryProductAtom, markedMemoryProductAtom_eq_zero_of_unrepresented _ _ _ _ _ hb]
    positivity

end ArtinMatthews

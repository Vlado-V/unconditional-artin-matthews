module

public import ArtinMatthews.MarkedMinorArcProductAtoms
public import ArtinMatthews.MarkedMinorArcWeightedConjugation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual product-mass square roots are bounded endpoint multipliers. -/
noncomputable section
namespace ArtinMatthews

open Filter Matrix
open scoped BigOperators Topology

theorem markedWeightedCountingMatrix_endpoint_scale {ι : Type*} (mass : ι → ℝ)
    (K : Matrix ι ι ℂ) {Y : ℝ} (hY : 0 < Y) (i j : ι) :
    markedWeightedCountingMatrix mass K i j =
      ((1/Y:ℝ):ℂ)*(Real.sqrt (Y*mass i):ℂ)*K i j*(Real.sqrt (Y*mass j):ℂ) := by
  have hr : Real.sqrt (mass i)*Real.sqrt (mass j) =
      (1/Y)*(Real.sqrt (Y*mass i)*Real.sqrt (Y*mass j)) := by
    rw [Real.sqrt_mul hY.le, Real.sqrt_mul hY.le]
    symm
    calc
      _ = ((Real.sqrt Y*Real.sqrt Y)/Y)*(Real.sqrt (mass i)*Real.sqrt (mass j)) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hY.le, div_self hY.ne', one_mul]
  have hc : (Real.sqrt (mass i):ℂ)*(Real.sqrt (mass j):ℂ) =
      ((1/Y:ℝ):ℂ)*((Real.sqrt (Y*mass i):ℂ)*(Real.sqrt (Y*mass j):ℂ)) := by
    exact_mod_cast hr
  unfold markedWeightedCountingMatrix
  calc
    _ = K i j*((Real.sqrt (mass i):ℂ)*(Real.sqrt (mass j):ℂ)) := by ring
    _ = _ := by rw [hc]; ring

theorem marked_actual_memory_endpoint_cutoff_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (b : ℕ),
      0 ≤ q → q ≤ 1 → 0 < Y → η ((b:ℝ)/Y) ≠ 0 →
      Real.sqrt (Y*markedActualMemoryProductAtom e q x b) ≤
        Real.sqrt ((4/Real.log 2)^(Fintype.card J)) := by
  filter_upwards [marked_actual_memory_product_atom_cutoff_eventually e he hinj η hη] with x hx
  intro q Y b hq0 hq1 hY hcut
  exact markedProductMass_sqrt_endpoint_le hY (hx q Y b hq0 hq1 hY hcut)

theorem marked_actual_memory_endpoint_pair_cutoff_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) (hinj : Function.Injective e)
    (η : ℝ → ℂ) (hη : Function.support η ⊆ Set.Icc 1 4) :
    ∀ᶠ x : ℝ in atTop, ∀ (q Y : ℝ) (a b : ℕ),
      0 ≤ q → q ≤ 1 → 0 < Y → η ((a:ℝ)/Y) ≠ 0 → η ((b:ℝ)/Y) ≠ 0 →
      Real.sqrt (markedActualMemoryProductAtom e q x a*markedActualMemoryProductAtom e q x b) ≤
        (4/Real.log 2)^(Fintype.card J)/Y := by
  filter_upwards [marked_actual_memory_product_atom_cutoff_eventually e he hinj η hη,
    marked_actual_memory_product_atom_nonneg_eventually e he] with x hx hn
  intro q Y a b hq0 hq1 hY hca hcb
  exact markedProductMass_sqrt_pair_le (hn q a hq0 hq1) (by positivity) hY
    (hx q Y a hq0 hq1 hY hca) (hx q Y b hq0 hq1 hY hcb)

end ArtinMatthews

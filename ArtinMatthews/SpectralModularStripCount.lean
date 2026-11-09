module

public import ArtinMatthews.SpectralModularStripCountBounds
public import ArtinMatthews.SpectralModularStripCountInjection
public import ArtinMatthews.SpectralCuspMass
public import Mathlib.Data.Set.Card


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine uniform quadratic bound for modular strip multiplicity near
height zero. Matrices are counted with their actual signs in SL(2,ℤ). -/
noncomputable section
open Set UpperHalfPlane
open scoped MatrixGroups
namespace ArtinMatthews

def spectralModularStripCodeBox (N : ℕ) (Y : ℝ) : Finset (ℤ×ℤ×ℤ) :=
  Finset.Icc (-⌊2/Y⌋) ⌊2/Y⌋ ×ˢ
    (Finset.Icc (-⌊2/Y⌋) ⌊2/Y⌋ ×ˢ Finset.Icc 0 (N : ℤ))

theorem spectralModularStripCode_mem_box (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hY1 : Y ≤ 1) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd)
    (g : SL(2,ℤ)) (hg : g • z ∈ hyperbolicCuspStrip (N : ℝ) Y) :
    spectralModularStripCode z g ∈ spectralModularStripCodeBox N Y := by
  obtain ⟨hc,hd⟩ := spectralModular_strip_bottom_row_bound g z hz Y hY hY1 hg.2
  have hrow (a : ℤ) (ha : |(a : ℝ)| ≤ 2/Y) : a ∈ Finset.Icc (-⌊2/Y⌋) ⌊2/Y⌋ := by
    have hu : a ≤ ⌊2/Y⌋ := Int.le_floor.mpr (abs_le.mp ha).2
    have hl : -a ≤ ⌊2/Y⌋ := Int.le_floor.mpr (by push_cast; linarith [(abs_le.mp ha).1])
    simp only [Finset.mem_Icc]
    omega
  have hre : ⌊(g • z).re⌋ ∈ Finset.Icc 0 (N : ℤ) := by
    apply Finset.mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr hg.1.1.le,?_⟩
    simpa using Int.floor_mono hg.1.2
  exact Finset.mem_product.mpr ⟨hrow _ hc,Finset.mem_product.mpr ⟨hrow _ hd,hre⟩⟩

theorem spectralModular_strip_finite (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hY1 : Y ≤ 1) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    {g : SL(2,ℤ) | g • z ∈ hyperbolicCuspStrip (N : ℝ) Y}.Finite := by
  apply ((spectralModularStripCodeBox N Y).finite_toSet.preimage
    (spectralModularStripCode_injective z).injOn).subset
  intro g hg
  exact spectralModularStripCode_mem_box N Y hY hY1 z hz g hg

theorem spectralModularStripCodeBox_card (N : ℕ) (Y : ℝ) (hY : 0 < Y) (hY1 : Y ≤ 1) :
    ((spectralModularStripCodeBox N Y).card : ℝ) ≤ 25*((N : ℝ)+1)/Y^2 := by
  let s := Finset.Icc (-⌊2/Y⌋) ⌊2/Y⌋
  have hB : 0 ≤ ⌊2/Y⌋ := Int.floor_nonneg.mpr (by positivity)
  have hs : (s.card : ℝ) = 2*(⌊2/Y⌋ : ℝ)+1 := by
    have hh := Int.card_Icc_of_le (a := -⌊2/Y⌋) (b := ⌊2/Y⌋) (by omega)
    calc
      _ = ((⌊2/Y⌋+1-(-⌊2/Y⌋) : ℤ) : ℝ) := by exact_mod_cast hh
      _ = _ := by push_cast; ring
  have hsB : (s.card : ℝ) ≤ 5/Y := by
    rw [hs]
    have hunit : (1:ℝ) ≤ 1/Y := (le_div_iff₀ hY).mpr (by simpa using hY1)
    calc
      _ ≤ 2*(2/Y)+1 := by linarith [Int.floor_le (2/Y)]
      _ ≤ 2*(2/Y)+1/Y := add_le_add le_rfl hunit
      _ = 5/Y := by ring
  have hn : (Finset.Icc (0 : ℤ) (N : ℤ)).card = N+1 := by
    rw [Int.card_Icc]
    omega
  have hcard : ((spectralModularStripCodeBox N Y).card : ℝ) = (s.card : ℝ)^2*((N : ℝ)+1) := by
    simp only [spectralModularStripCodeBox,Finset.card_product,hn,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    dsimp only [s]
    ring
  rw [hcard]
  calc
    _ ≤ (5/Y)^2*((N : ℝ)+1) := mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (Nat.cast_nonneg s.card) (by positivity)).mpr hsB) (by positivity)
    _ = _ := by ring

theorem spectralModular_strip_ncard_le (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hY1 : Y ≤ 1) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    ({g : SL(2,ℤ) | g • z ∈ hyperbolicCuspStrip (N : ℝ) Y}.ncard : ℝ) ≤
      25*((N : ℝ)+1)/Y^2 := by
  have hc := Set.ncard_le_ncard_of_injOn (spectralModularStripCode z)
    (fun g hg => spectralModularStripCode_mem_box N Y hY hY1 z hz g hg)
    (spectralModularStripCode_injective z).injOn (spectralModularStripCodeBox N Y).finite_toSet
  rw [Set.ncard_coe_finset] at hc
  exact (show (_ : ℝ) ≤ ((spectralModularStripCodeBox N Y).card : ℝ) by exact_mod_cast hc).trans
    (spectralModularStripCodeBox_card N Y hY hY1)

theorem spectralModular_inverse_strip_finite (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hY1 : Y ≤ 1) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    {g : SL(2,ℤ) | g⁻¹ • z ∈ hyperbolicCuspStrip (N : ℝ) Y}.Finite :=
  (spectralModular_strip_finite N Y hY hY1 z hz).preimage
    (f := fun g : SL(2,ℤ) => g⁻¹) inv_injective.injOn

theorem spectralModular_inverse_strip_ncard_le (N : ℕ) (Y : ℝ) (hY : 0 < Y)
    (hY1 : Y ≤ 1) (z : UpperHalfPlane) (hz : z ∈ ModularGroup.fd) :
    ({g : SL(2,ℤ) | g⁻¹ • z ∈ hyperbolicCuspStrip (N : ℝ) Y}.ncard : ℝ) ≤
      25*((N : ℝ)+1)/Y^2 := by
  have hc := Set.ncard_le_ncard_of_injOn (fun g : SL(2,ℤ) => g⁻¹)
    (fun _ hg => hg) inv_injective.injOn (spectralModular_strip_finite N Y hY hY1 z hz)
  exact (show (_ : ℝ) ≤ ({g : SL(2,ℤ) | g • z ∈ hyperbolicCuspStrip (N : ℝ) Y}.ncard : ℝ)
    by exact_mod_cast hc).trans (spectralModular_strip_ncard_le N Y hY hY1 z hz)

end ArtinMatthews

module

public import ArtinMatthews.GiantSignedGhostCoordinateGrowth
public import ArtinMatthews.GiantSignedGhostProductSymmetry


set_option backward.privateInPublic true
@[expose] public section

/-! Finite products of actual coordinate ghosts on every pending degree. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B] {P : B → Finset ℕ}

def giantSignedGhostCoordinateWord (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) :
    List B → (GiantSignedMemoryGroups P → ℂ) → GiantSignedMemoryGroups P → ℂ
  | [], f => f
  | g :: gs, f => giantSignedGhostCoordinateApply ν A C D g
      (giantSignedGhostCoordinateWord ν A C D gs f)

theorem giantSignedGhostCoordinateWord_exponential
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (gs : List B) (f : GiantSignedMemoryGroups P → ℂ)
    (hf : GiantSignedGhostProductExponential f) :
    GiantSignedGhostProductExponential (giantSignedGhostCoordinateWord ν A C D gs f) := by
  induction gs with
  | nil => exact hf
  | cons g gs ih => exact giantSignedGhostCoordinateApply_exponential ν hν A C D g _ ih

omit [Fintype B] in
theorem giantSignedGhostCoordinateWord_symmetric
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (gs : List B)
    (f : GiantSignedMemoryGroups P → ℂ) (hf : GiantSignedGhostProductSymmetric f) :
    GiantSignedGhostProductSymmetric (giantSignedGhostCoordinateWord ν A C D gs f) := by
  induction gs with
  | nil => exact hf
  | cons g gs ih => exact giantSignedGhostCoordinateApply_symmetric ν A C D g _ ih

def giantSignedGhostMemoryApply (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (m : GiantSignedMemory P) : ℂ :=
  giantSignedGhostCoordinateWord ν A C D Finset.univ.toList
    (fun x => f ((giantSignedMemoryGroupEquiv P).symm x)) (giantSignedMemoryGroupEquiv P m)

theorem giantSignedGhostMemoryApply_symmetric
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ)
    (f : GiantSignedMemory P → ℂ) (hf : GiantSignedMemorySymmetric f) :
    GiantSignedMemorySymmetric (giantSignedGhostMemoryApply ν A C D f) :=
  giantSignedGhostProductSymmetric_memory _
    (giantSignedGhostCoordinateWord_symmetric ν A C D _ _
      (giantSignedMemorySymmetric_group_fibers f hf))

theorem giantSignedGhostMemoryApply_empty [IsEmpty B]
    (ν : ∀ g, P g → ℝ) (A C D : B → ℂ) (f : GiantSignedMemory P → ℂ) :
    giantSignedGhostMemoryApply ν A C D f = f := by
  funext m
  simp only [giantSignedGhostMemoryApply, Finset.univ_eq_empty,
    Finset.toList_empty, giantSignedGhostCoordinateWord, Equiv.symm_apply_apply]

variable [∀ (g : B) (p : P g), NeZero p.val]

theorem giantSignedGhostCoordinateWord_energy
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ∀ g, ‖A g‖ + ‖C g‖ / v ≤ 1)
    (gs : List B) (f : GiantSignedMemoryGroups P → ℂ)
    (hfs : GiantSignedGhostProductSymmetric f) (hfe : GiantSignedGhostProductExponential f) :
    giantSignedGhostProductEnergy ν (giantSignedGhostCoordinateWord ν A C D gs f) ≤
      (gs.map (fun g => ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) *
        (∑ p : P g, ν g p) * v)))).prod * giantSignedGhostProductEnergy ν f := by
  induction gs with
  | nil => simp only [giantSignedGhostCoordinateWord, List.map_nil, List.prod_nil, one_mul, le_refl]
  | cons g gs ih =>
    have hs := giantSignedGhostCoordinateWord_symmetric ν A C D gs f hfs
    obtain ⟨Cf, u, hCf, hu, hf⟩ := giantSignedGhostCoordinateWord_exponential ν hν A C D gs f hfe
    have he := giantSignedGhostCoordinateApply_energy ν hν A C D g v hv (hrow g) (hcol g)
      (giantSignedGhostCoordinateWord ν A C D gs f) hs Cf u hCf hu hf
    apply he.trans
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using
      (mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) *
        (∑ p : P g, ν g p) * v)))) ih)

theorem giantSignedGhostMemoryApply_energy
    (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ∀ g, ‖A g‖ + ‖C g‖ / v ≤ 1)
    (f : GiantSignedMemory P → ℂ) (hfs : GiantSignedMemorySymmetric f)
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hf : ∀ m, ‖f m‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedGhostMemoryEnergy ν (giantSignedGhostMemoryApply ν A C D f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : P g, ν g p) * v))) *
        giantSignedGhostMemoryEnergy ν f := by
  let F := fun x => f ((giantSignedMemoryGroupEquiv P).symm x)
  have hF : GiantSignedGhostProductExponential F := ⟨Cf, u, hCf, hu, fun x => hf _⟩
  have he := giantSignedGhostCoordinateWord_energy ν hν A C D v hv hrow hcol Finset.univ.toList F
    (giantSignedMemorySymmetric_group_fibers f hfs) hF
  rw [giantSignedGhostMemoryEnergy_groups, giantSignedGhostMemoryEnergy_groups]
  simpa only [giantSignedGhostMemoryApply, Equiv.apply_symm_apply, Finset.prod_map_toList] using he

end
end ArtinMatthews

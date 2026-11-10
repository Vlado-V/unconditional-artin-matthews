module

public import ArtinMatthews.UnitTorusLocalRellich


set_option backward.privateInPublic true
@[expose] public section

/-! The half-open normalized torus cell and its full Lebesgue pullback. -/
namespace ArtinMatthews
open MeasureTheory UnitAddTorus Set
open scoped ENNReal
noncomputable section

variable (ι : Type*) [Fintype ι]

private theorem unitTorus_shiftedCellProjection_measurePreserving (a : ι → ℝ) :
    MeasurePreserving (unitTorusUnitCellProjection ι)
      ((volume : Measure (ι → ℝ)).restrict (Set.univ.pi fun i => Ioc (a i) (a i + 1)))
      (unitTorusHaar ι) := by
  have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
  rw [show (volume : Measure (ι → ℝ)) = Measure.pi (fun _ : ι => (volume : Measure ℝ)) from rfl,
    Measure.restrict_pi_pi]
  exact measurePreserving_pi _ _ fun i => by
    simpa only [hv] using UnitAddCircle.measurePreserving_mk (a i)

/-- Every Haar-almost-everywhere statement pulls back to the whole real space. -/
theorem unitTorusUnitCellProjection_ae_volume {P : UnitAddTorus ι → Prop}
    (h : ∀ᵐ t ∂unitTorusHaar ι, P t) :
    ∀ᵐ x ∂(volume : Measure (ι → ℝ)), P (unitTorusUnitCellProjection ι x) := by
  let S (k : ι → ℤ) : Set (ι → ℝ) :=
    Set.univ.pi fun i => Ioc (k i : ℝ) ((k i : ℝ) + 1)
  have hcover : (⋃ k, S k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    refine Set.mem_iUnion.mpr ⟨fun i => ⌈x i⌉ - 1, ?_⟩
    intro i _
    change (↑(⌈x i⌉ - 1 : ℤ) : ℝ) < x i ∧ x i ≤ (↑(⌈x i⌉ - 1 : ℤ) : ℝ) + 1
    push_cast
    exact ⟨by linarith [Int.ceil_lt_add_one (x i)], by linarith [Int.le_ceil (x i)]⟩
  have hs : ∀ k, ∀ᵐ x ∂(volume : Measure (ι → ℝ)).restrict (S k),
      P (unitTorusUnitCellProjection ι x) := by
    intro k
    exact (unitTorus_shiftedCellProjection_measurePreserving ι
      (fun i => (k i : ℝ))).quasiMeasurePreserving.ae h
  have hfull := (ae_restrict_iUnion_iff S (fun x => P (unitTorusUnitCellProjection ι x))).2 hs
  simpa only [hcover, Measure.restrict_univ] using hfull

/-- Membership in (L^p) on the literal unit cell descends to the torus. -/
theorem unitTorus_memLp_of_unitCell (F : UnitAddTorus ι → ℂ) (p : ℝ≥0∞)
    (hF : MemLp (F ∘ unitTorusUnitCellProjection ι) p (unitTorusUnitCellMeasure ι)) :
    MemLp F p (unitTorusHaar ι) := by
  let a : ι → ℝ := 0
  let S : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}
  have hS : MeasurableSet S := MeasurableSet.univ_pi' fun _ => measurableSet_Ioc
  have hcell : (volume : Measure (ι → ℝ)).restrict S = unitTorusUnitCellMeasure ι := by
    rw [show S = Set.univ.pi (fun _ : ι => Ioc (0 : ℝ) 1) by ext x; simp [S, a]]
    exact Measure.restrict_pi_pi _ _
  let e := UnitAddTorus.measurableEquivPiIoc a
  have hcoe : MeasurePreserving (Subtype.val : S → (ι → ℝ))
      (Measure.comap Subtype.val volume) (unitTorusUnitCellMeasure ι) := by
    rw [← hcell]
    exact measurePreserving_subtype_coe hS
  have he : MeasurePreserving e (unitTorusHaar ι) (Measure.comap Subtype.val volume) :=
    UnitAddTorus.measurePreserving_equivPiIoc a
  have h : MemLp (fun t => F (unitTorusUnitCellProjection ι (e t).val))
      p (unitTorusHaar ι) := (hF.comp_measurePreserving hcoe).comp_measurePreserving he
  exact MemLp.ae_eq (Filter.Eventually.of_forall fun t => congrArg F (e.symm_apply_apply t)) h

end
end ArtinMatthews

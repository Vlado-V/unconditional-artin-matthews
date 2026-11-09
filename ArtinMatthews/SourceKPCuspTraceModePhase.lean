module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceKPCuspPrincipalCellIntegral
public import Mathlib.Topology.Instances.RealVectorSpace


set_option backward.privateInPublic true
@[expose] public section

/-! The standard adelic character on the actual scaled Minkowski cell has
exactly the integer Fourier phase given by the trace-dual basis. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Classical BigOperators ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "E" => mixedEmbedding.mixedSpace K

theorem sourceKPCuspTraceFrequency_zero_iff (d : 𝓞 K) (hd : d ≠ 0) (n : I → ℤ) :
    sourceKPCuspTraceFrequency K d n = 0 ↔ n = 0 := by
  constructor
  · intro hm
    by_contra hn
    exact sourceKPCuspTraceFrequency_ne_zero K d hd hn hm
  · rintro rfl
    simp [sourceKPCuspTraceFrequency, idealTraceIntegerLift]

theorem sourceKPCuspArchTrace_mixed (m : K) (x : E) :
    archTrace K (algebraMap K (InfiniteAdeleRing K) m *
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x) = sourceKPCuspTraceFunctional K m x := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let L : E →+ ℝ :=
    { toFun := fun z => archTrace K (algebraMap K (InfiniteAdeleRing K) m * e.symm z)
      map_zero' := by simp
      map_add' := fun z w => by simp only [map_add, mul_add] }
  have hLc : Continuous L :=
    (archTrace_continuous K).comp
      (continuous_const.mul (ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K).symm.continuous)
  let Lr := L.toRealLinearMap hLc
  have heq : Lr.toLinearMap = (sourceKPCuspTraceFunctional K m).toLinearMap := by
    apply (mixedEmbedding.latticeBasis K).ext
    intro i
    rw [mixedEmbedding.latticeBasis_apply]
    let a := integralBasis K i
    change archTrace K (algebraMap K (InfiniteAdeleRing K) m * e.symm (mixedEmbedding K a)) =
      sourceKPCuspTraceFunctional K m (mixedEmbedding K a)
    have ha : e.symm (mixedEmbedding K a) = algebraMap K (InfiniteAdeleRing K) a :=
      congrArg Prod.fst (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_rational K a)
    rw [ha, ← map_mul, archTrace_rational, sourceKPCuspTraceFunctional_embedding, mul_comm a m]
  exact congrArg (fun f : E →ₗ[ℝ] ℝ => f x) heq

theorem sourceKPCuspTraceFrequency_unitCell_phase (d : 𝓞 K) (hd : d ≠ 0)
    (n : I → ℤ) (x : I → ℝ) :
    character K (algebraMap K 𝔸[K] (sourceKPCuspTraceFrequency K d n) *
        sourceKPCuspUnitCellAdelicPoint K d hd x) =
      UnitAddTorus.mFourier n (unitTorusUnitCellProjection I x) := by
  let m := sourceKPCuspTraceFrequency K d n
  let z := (sourceKPCuspCoordinates K d hd).symm x
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  have hmul : algebraMap K 𝔸[K] m * sourceKPCuspUnitCellAdelicPoint K d hd x =
      ((algebraMap K (InfiniteAdeleRing K) m * e.symm z,0) : 𝔸[K]) :=
    Prod.ext rfl (mul_zero _)
  have htrace : archTrace K (algebraMap K (InfiniteAdeleRing K) m * e.symm z) =
      ∑ i, x i * (n i : ℝ) := by
    rw [sourceKPCuspArchTrace_mixed, sourceKPCuspTraceFunctional_coordinates]
    change (∑ i, (sourceKPCuspCoordinates K d hd) ((sourceKPCuspCoordinates K d hd).symm x) i *
      (n i : ℝ)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  change character K (algebraMap K 𝔸[K] m * sourceKPCuspUnitCellAdelicPoint K d hd x) = _
  rw [hmul, character_arch]
  change Complex.exp ((archTrace K (algebraMap K (InfiniteAdeleRing K) m * e.symm z) : ℂ) *
    (2 * (Real.pi : ℂ) * Complex.I)) = _
  rw [htrace]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, unitTorusUnitCellProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem sourceKPCuspTraceFrequency_unitCell_star_phase (d : 𝓞 K) (hd : d ≠ 0)
    (n : I → ℤ) (x : I → ℝ) :
    star (character K (algebraMap K 𝔸[K] (sourceKPCuspTraceFrequency K d n) *
        sourceKPCuspUnitCellAdelicPoint K d hd x)) =
      UnitAddTorus.mFourier (-n) (unitTorusUnitCellProjection I x) := by
  rw [sourceKPCuspTraceFrequency_unitCell_phase, UnitAddTorus.mFourier_neg]
  rfl

end
end ArtinMatthews

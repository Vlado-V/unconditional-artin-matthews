module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceKPCuspPoincare


set_option backward.privateInPublic true
@[expose] public section

/-! Cartesian cusp derivatives reconstructed from the genuine scaled-lattice derivatives. -/
namespace ArtinMatthews
open NumberField Module Module.Free MeasureTheory Topology
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) [IsTotallyComplex K]
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance sourceKPCuspCartesianQuotientMeasurable : MeasurableSpace Q := borel Q
local instance sourceKPCuspCartesianQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspCartesianDerivativeC (g : I → C(Q, ℂ)) (v : InfinitePlace K) (k : Fin 2) : C(Q, ℂ) :=
  ∑ i, ((sourceKPCuspCoordinates K d hd (sourceKPCuspHorizontalDirection K v k)) i : ℂ) • g i

theorem sourceKPCuspCartesianDerivativeC_hasDerivAt
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g)
    (hF : Differentiable ℝ (fun x : E => f (sourceKPCuspArchQuotientMap K d x)))
    (v : InfinitePlace K) (k : Fin 2) (x : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (sourceKPCuspArchQuotientMap K d
      (x + u • sourceKPCuspHorizontalDirection K v k)))
      (sourceKPCuspCartesianDerivativeC K d hd g v k
        (sourceKPCuspArchQuotientMap K d (x + t • sourceKPCuspHorizontalDirection K v k))) t := by
  let F : E → ℂ := fun x => f (sourceKPCuspArchQuotientMap K d x)
  let e := sourceKPCuspHorizontalDirection K v k
  let p := x + t • e
  have hb (i : I) : fderiv ℝ F p (sourceKPCuspLatticeBasis K d hd i) =
      g i (sourceKPCuspArchQuotientMap K d p) := by
    have h1 := (hF (p + (0 : ℝ) • sourceKPCuspLatticeBasis K d hd i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const (sourceKPCuspLatticeBasis K d hd i)).const_add p)
    have h2 := hfg i p 0
    simpa only [Function.comp_def, zero_smul, add_zero, one_smul, F] using h1.unique h2
  have hD : fderiv ℝ F p e = sourceKPCuspCartesianDerivativeC K d hd g v k
      (sourceKPCuspArchQuotientMap K d p) := by
    conv_lhs => rw [← (sourceKPCuspLatticeBasis K d hd).sum_repr e]
    simp only [map_sum, map_smul, hb]
    simp only [sourceKPCuspCartesianDerivativeC, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    change (sourceKPCuspCoordinates K d hd e i) • g i (sourceKPCuspArchQuotientMap K d p) = _
    simp [Algebra.smul_def, e]
  have h := (hF p).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const e).const_add x)
  have h' : HasDerivAt (fun u : ℝ => F (x + u • e)) (fderiv ℝ F p e) t := by
    simpa only [Function.comp_def, id_eq, one_smul, F] using h
  exact h'.congr_deriv hD

end
end ArtinMatthews

module

public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceKPLocalFiberIntegral
public import ArtinMatthews.SourceKubotaGL2Generation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The archimedean Weyl factor has spherical value one. Thus the
actual finite-kernel fiber inherits the proved local scattering law. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical SourceArchJacquet Matrix
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPLocalArchWeyl_spherical (s : ℂ) :
    sourceArchSphericalSection s sourcePGL2Weyl = 1 := by
  change sourceArchSphericalGL s (sourceGL2Weyl : GL (Fin 2) ℂ) = 1
  simp [sourceArchSphericalGL, sourceArchHeight, sourceArchBottomNorm,
    sourceGL2Weyl, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem sourceKPLocalArchKernel_zero (s : ℂ) :
    sourceKPArchIntertwiningKernel K hζ s 1 0 = 1 := by
  rw [sourceKPArchIntertwiningKernel_product]
  apply Finset.prod_eq_one
  intro v _
  have hz : sourceKPArchComplexEquiv K hζ v ((0 : InfiniteAdeleRing K) v) = 0 := by
    change sourceKPArchComplexEquiv K hζ v (0 : v.Completion) = 0
    exact map_zero _
  simpa only [hz, map_one, sourcePGL2Upper, sourceGL2Upper_zero,
    mul_one] using sourceKPLocalArchWeyl_spherical s

theorem sourceKPLocalFiniteKernel_eq_full (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ) (y : 𝔸ᶠ[K]) :
    ((sourceKPAdelicCompactSection K hζ s).val
      (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (0,y) * (1,g))).val 1 =
        sourceKPFiniteIntertwiningKernel K hζ s g y := by
  have h : ((sourceKPAdelicCompactSection K hζ s).val
      (sourceKPAdelicProjectiveWeyl K hζ * sourceKPAdelicUpperLift K hζ (0,y) * (1,g))).val 1 =
      sourceKPArchIntertwiningKernel K hζ s 1 0 * sourceKPFiniteIntertwiningKernel K hζ s g y :=
    sourceKPAdelicIntertwiningKernel_arch_finite K hζ s (show SourceKPAdelicProjective K hζ from (1,g))
      (show 𝔸[K] from (0,y))
  exact h.trans ((congrArg (fun c => c * sourceKPFiniteIntertwiningKernel K hζ s g y)
    (sourceKPLocalArchKernel_zero K hζ s)).trans (one_mul _))

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

theorem sourceKPLocalFiniteKernel_integrable (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val (1,g) = 1)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    Integrable (fun x : P.val.adicCompletion K => sourceKPFiniteIntertwiningKernel K hζ s g
      (sourceKPFiniteAdditiveSingle K P.val x+r))
      (sourceJacquetHaar K P.val) := by
  have h := sourceKPLocalFiber_integrable K hζ S₀ P s r hr (1,g) hg 1 hP hs
  simpa only [sourceKPLocalFiniteKernel_eq_full] using h

theorem sourceKPLocalFiniteKernel_integral_eq_factor_unit_ball (s : ℂ)
    (g : SourceKPFiniteAdeleProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val (1,g) = 1)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0)
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) :
    (∫ x : P.val.adicCompletion K, sourceKPFiniteIntertwiningKernel K hζ s g
      (sourceKPFiniteAdditiveSingle K P.val x+r)
      ∂sourceJacquetHaar K P.val) =
      sourceKPUnramifiedScatteringFactor P.val s *
        ∫ x : P.val.adicCompletion K in sourceLocalBall K P.val 0,
          sourceKPFiniteIntertwiningKernel K hζ s g
            (sourceKPFiniteAdditiveSingle K P.val x+r)
          ∂sourceJacquetHaar K P.val := by
  have h := sourceKPLocalFiber_integral_eq_factor_unit_ball K hζ S₀ P s r hr (1,g) hg 1 hP hs
  simpa only [sourceKPLocalFiniteKernel_eq_full] using h

end
end ArtinMatthews

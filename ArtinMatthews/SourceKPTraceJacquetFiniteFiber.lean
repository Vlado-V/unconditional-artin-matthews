module

public import ArtinMatthews.SourceKPTraceJacquetLocalFinite
public import ArtinMatthews.SourceKPTraceJacquetArchFinite
public import ArtinMatthews.SourceKPLocalFiniteKernel
public import ArtinMatthews.SourceFiniteCompactRemoval


set_option backward.privateInPublic true
@[expose] public section

/-! The local ordinary Jacquet value acts through the actual
three-basis receiver on each global torus coordinate. The finite
remainder and its trace phase are retained in the literal fiber. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPTraceJacquetFrequencyAt (P : HeightOneSpectrum (𝓞 K)) (m : Kˣ) :
    (P.adicCompletion K)ˣ :=
  Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom m

theorem sourceKPTraceJacquetFiniteCharacter_single_add (P : HeightOneSpectrum (𝓞 K))
    (m : Kˣ) (x : P.adicCompletion K) (r : 𝔸ᶠ[K]) :
    sourceKPTraceJacquetFiniteCharacter K m (sourceKPFiniteAdditiveSingle K P x+r) =
      star (localFiniteCharacter K P ((sourceKPTraceJacquetFrequencyAt K P m : P.adicCompletion K)*x)) *
        sourceKPTraceJacquetFiniteCharacter K m r := by
  let y := (sourceKPTraceJacquetFrequencyAt K P m : P.adicCompletion K)*x
  have hm : algebraMap K 𝔸ᶠ[K] (m : K) * sourceKPFiniteAdditiveSingle K P x =
      sourceKPFiniteAdditiveSingle K P y := by
    apply FiniteAdeleRing.ext
    intro Q
    change (algebraMap K 𝔸ᶠ[K] (m : K)) Q * sourceKPFiniteAdditiveSingle K P x Q =
      sourceKPFiniteAdditiveSingle K P y Q
    by_cases hQ : Q = P
    · subst Q
      rw [sourceKPFiniteAdditiveSingle_same K P x, sourceKPFiniteAdditiveSingle_same K P y,
        FiniteAdeleRing.algebraMap_apply] <;> rfl
    · rw [sourceKPFiniteAdditiveSingle_other K P x Q hQ,
        sourceKPFiniteAdditiveSingle_other K P y Q hQ, mul_zero]
  have hsingle : finiteCharacter K (sourceKPFiniteAdditiveSingle K P y) = localFiniteCharacter K P y :=
    (localFiniteCharacter_single K P y).symm
  unfold sourceKPTraceJacquetFiniteCharacter
  rw [mul_add, AddChar.map_add_eq_mul, star_mul', hm, hsingle]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "L" => P.val.adicCompletion K
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "ψ₀" => localFiniteCharacter K P.val

theorem sourceKPTraceJacquetLocalRest_integral
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) (m : Lˣ)
    (r : SourceKPAdelicProjective K hζ) (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    Integrable (fun x : L => ψ₀ (-((m : L)*x)) *
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*r)).val t) μ₀ ∧
    (∫ x : L, ψ₀ (-((m : L)*x)) *
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*r)).val t ∂μ₀) =
      sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s r hr) t
        (sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s m) := by
  let v := sourceKPLocalRestVector K hζ S₀ P s r hr
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s v t
  let I := sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s (m : L)
  have hi : Integrable I μ₀ :=
    sourceKPTraceJacquetLocalOrdinaryIntegrand_integrable K hζ S₀ P hP hs (m : L)
  have he (x : L) : ψ₀ (-((m : L)*x)) *
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*r)).val t = A (I x) := by
    rw [sourceKPLocalRest_section K hζ S₀ P s r hr, sourceKPLocalReceiverIntertwining_apply]
    change _ = A (sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s (m : L) x)
    rw [sourceKPTraceJacquetLocalOrdinaryIntegrand_eq_spherical, map_smul,
      sourceKPTraceJacquetFinitePhase_star_eq_neg K]
    rfl
  refine ⟨(A.integrable_comp hi).congr (Filter.Eventually.of_forall fun x => (he x).symm), ?_⟩
  simp_rw [he]
  rw [A.integral_comp_comm hi]
  exact congrArg A (sourceKPTraceJacquetLocalOrdinary_eq_finite K hζ S₀ P hP hs m)

theorem sourceKPTraceJacquetGlobalFiber_integral
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) (m : Kˣ)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) (g : SourceKPAdelicProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val g = 1)
    (t : sourceKPAdelicCoveringTorus K hζ) :
    let R := sourceKPLocalFiberRest K hζ P.val r g
    let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g hg
    Integrable (fun x : L => sourceKPTraceJacquetFiniteCharacter K m (sourceKPFiniteAdditiveSingle K P.val x+r) *
      ((F₀).val (W₀ * sourceKPAdelicUpperLift K hζ (0,sourceKPFiniteAdditiveSingle K P.val x+r)*g)).val t) μ₀ ∧
    (∫ x : L, sourceKPTraceJacquetFiniteCharacter K m (sourceKPFiniteAdditiveSingle K P.val x+r) *
      ((F₀).val (W₀ * sourceKPAdelicUpperLift K hζ (0,sourceKPFiniteAdditiveSingle K P.val x+r)*g)).val t ∂μ₀) =
      sourceKPTraceJacquetFiniteCharacter K m r *
        sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s R hR) t
          (sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (sourceKPTraceJacquetFrequencyAt K P.val m)) := by
  let R := sourceKPLocalFiberRest K hζ P.val r g
  let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g hg
  let mP := sourceKPTraceJacquetFrequencyAt K P.val m
  let C := sourceKPTraceJacquetFiniteCharacter K m r
  let v := sourceKPLocalRestVector K hζ S₀ P s R hR
  let A := sourceKPLocalReceiverCoordinate K hζ S₀ P s v t
  let k := fun x : L => ψ₀ (-((mP : L)*x)) *
    ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*R)).val t
  have he (x : L) : sourceKPTraceJacquetFiniteCharacter K m (sourceKPFiniteAdditiveSingle K P.val x+r) *
      ((F₀).val (W₀ * sourceKPAdelicUpperLift K hζ (0,sourceKPFiniteAdditiveSingle K P.val x+r)*g)).val t =
      C*k x := by
    rw [sourceKPTraceJacquetFiniteCharacter_single_add K P.val m x r, sourceKPLocalFiber_factor K hζ P.val x r g,
      sourceKPTraceJacquetFinitePhase_star_eq_neg K]
    change (ψ₀ (-((mP : L)*x))*C) *
      ((F₀).val (ι₀ (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))*R)).val t = _
    dsimp only [k]
    ring
  have h := sourceKPTraceJacquetLocalRest_integral K hζ S₀ P s hP hs mP R hR t
  refine ⟨(h.1.const_mul C).congr (Filter.Eventually.of_forall fun x => (he x).symm),?_⟩
  conv_lhs => simp only [he]
  rw [integral_const_mul]
  exact congrArg (C*·) h.2

theorem sourceKPTraceJacquetFiniteFiber_integral
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) (m : Kˣ)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) (g : SourceKPFiniteAdeleProjective K hζ)
    (hg : sourceKPAdelicLocalBase K hζ P.val (1,g) = 1) :
    let R := sourceKPLocalFiberRest K hζ P.val r (1,g)
    let hR := sourceKPLocalFiberRest_base K hζ P.val r hr (1,g) hg
    Integrable (fun x : L => sourceKPTraceJacquetFiniteKernel K hζ m s g
      (sourceKPFiniteAdditiveSingle K P.val x+r)) μ₀ ∧
    (∫ x : L, sourceKPTraceJacquetFiniteKernel K hζ m s g
      (sourceKPFiniteAdditiveSingle K P.val x+r) ∂μ₀) =
      sourceKPTraceJacquetFiniteCharacter K m r *
        sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s R hR) 1
          (sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (sourceKPTraceJacquetFrequencyAt K P.val m)) := by
  have h := sourceKPTraceJacquetGlobalFiber_integral K hζ S₀ P s hP hs m r hr (1,g) hg 1
  simpa only [sourceKPTraceJacquetFiniteKernel, sourceKPLocalFiniteKernel_eq_full] using h

theorem sourceKPTraceJacquetFiniteFiber_of_integral_representative
    (hP : P.val ∉ traceBadPlaces K) (hs : 0 < s.re) (m : Kˣ)
    (r : 𝔸ᶠ[K]) (hr : r P.val = 0) (a : SourceKPFiniteAdeleCover K hζ)
    (k : SourceFiniteKP2Integral K P.val) (hk : k.val = sourceKPAdeleMatrixAt K P.val a.base) :
    let h₆ := source_exterior_six_not_mem K S₀ P.val P.property
    let g := sourceKPFiniteAdeleProjectiveMk K hζ a
    let g' := sourceKPFiniteCompactRemove K hζ P.val h₆ g k
    let hg' := sourceKPFiniteCompactRemove_base K hζ P.val h₆ a k hk
    let R := sourceKPLocalFiberRest K hζ P.val r g'
    let hR := sourceKPLocalFiberRest_base K hζ P.val r hr g' hg'
    Integrable (fun x : L => sourceKPTraceJacquetFiniteKernel K hζ m s g
      (sourceKPFiniteAdditiveSingle K P.val x+r)) μ₀ ∧
    (∫ x : L, sourceKPTraceJacquetFiniteKernel K hζ m s g
      (sourceKPFiniteAdditiveSingle K P.val x+r) ∂μ₀) =
      sourceKPTraceJacquetFiniteCharacter K m r *
        sourceKPLocalReceiverCoordinate K hζ S₀ P s (sourceKPLocalRestVector K hζ S₀ P s R hR) 1
          (sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (sourceKPTraceJacquetFrequencyAt K P.val m)) := by
  let h₆ := source_exterior_six_not_mem K S₀ P.val P.property
  let g := sourceKPFiniteAdeleProjectiveMk K hζ a
  let g' := sourceKPFiniteCompactRemove K hζ P.val h₆ g k
  have hg' := sourceKPFiniteCompactRemove_base K hζ P.val h₆ a k hk
  have he (x : 𝔸ᶠ[K]) : sourceKPTraceJacquetFiniteCharacter K m x *
      ((F₀).val (W₀ * sourceKPAdelicUpperLift K hζ (0,x)*g')).val 1 =
        sourceKPTraceJacquetFiniteKernel K hζ m s g x := by
    rw [show g' = (1,g'.2) from sourceKPFiniteCompactRemove_eq_pair K hζ P.val h₆ g k,
      sourceKPLocalFiniteKernel_eq_full]
    unfold sourceKPTraceJacquetFiniteKernel
    rw [sourceKPFiniteCompactRemove_kernel K hζ P.val h₆ s g k x]
  have h := sourceKPTraceJacquetGlobalFiber_integral K hζ S₀ P s hP hs m r hr g' hg' 1
  refine ⟨h.1.congr (Filter.Eventually.of_forall fun x => he (sourceKPFiniteAdditiveSingle K P.val x+r)),?_⟩
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (he (sourceKPFiniteAdditiveSingle K P.val x+r)).symm)) h.2

end
end ArtinMatthews

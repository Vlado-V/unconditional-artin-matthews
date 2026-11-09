module

public import ArtinMatthews.SourceKPAdelicOutgoingRetainedBorel
public import ArtinMatthews.SourceKPAdelicOutgoingRetainedProjection
public import ArtinMatthews.SourceKPAdelicExceptionalLocalNorm


set_option backward.privateInPublic true
@[expose] public section

/-! At a retained place the actual outgoing section gives a vector
in the local induced space with its proved deep level. The local
Borel values retain every other-place input and every torus coordinate. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

private def sourceKPOutgoingSingletonTuple {α : Type} (F : α → Type)
    [∀ a, Monoid (F a)] (p : α) : F p →* ((q : ↥({p} : Finset α)) → F q.val) :=
  MonoidHom.mulSingle (fun q : ↥({p} : Finset α) => F q.val) ⟨p, Finset.mem_singleton_self p⟩

private theorem sourceKPOutgoingSingletonTuple_lift {α M : Type} [Monoid M]
    (F : α → Type) [∀ a, Monoid (F a)] (φ : ∀ a, F a →* M) (p : α) (x : F p) :
    MonoidHom.noncommPiCoprod (fun q : ↥({p} : Finset α) => φ q.val)
      (fun {q r} h _ _ => (h (Subtype.ext
        ((Finset.mem_singleton.mp q.property).trans (Finset.mem_singleton.mp r.property).symm))).elim)
      (sourceKPOutgoingSingletonTuple F p x) = φ p x :=
  MonoidHom.noncommPiCoprod_mulSingle (fun q : ↥({p} : Finset α) => φ q.val)
    ⟨p, Finset.mem_singleton_self p⟩ x

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

local notation "S" => (Singleton.singleton P : Finset (HeightOneSpectrum (𝓞 K)))
local notation "G₀" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "G" => SourceKPAdelicProjective K hζ
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P
local notation "L" => sourceKPLocalCompactProductLift K hζ S
local notation "Rest" => SourceKPAdelicOutgoingRetainedRest K hζ S
local notation "V" => SourceKPAdelicTorusInducedSpace K hζ
local notation "Vₚ" => SourceKPAdelicPrincipalSeries K hζ
local notation "R" => sourceKPAdelicOutgoingRegularizedSection K hζ
local notation "W" => sourceKPAdelicOutgoingRegularizedRetainedCarrier K hζ S
local notation "J₀" => sourceKPLocalCompactDeepCoverLevel K hζ P
local notation "D" => sourceKPAdelicDeepCompact K hζ

abbrev sourceKPAdelicOutgoingSingletonPlace : ↥S := ⟨P, Finset.mem_singleton_self P⟩

local notation "p₀" => sourceKPAdelicOutgoingSingletonPlace K P
local notation "LocalGroup" => (fun Q : ↥S => SourceFiniteKP2Projective K hζ (Subtype.val Q))
local notation "LocalBorel" => (fun Q : ↥S => SourceFiniteKPProjectiveBorel K hζ (Subtype.val Q))

def sourceKPAdelicOutgoingLocalGroupTuple : G₀ →* SourceKPLocalCompactProductGroup K hζ S :=
  sourceKPOutgoingSingletonTuple (fun Q : HeightOneSpectrum (𝓞 K) => SourceFiniteKP2Projective K hζ Q) P

def sourceKPAdelicOutgoingLocalBorelTuple : B₀ →* SourceKPLocalCompactProductBorel K hζ S :=
  sourceKPOutgoingSingletonTuple (fun Q : HeightOneSpectrum (𝓞 K) => SourceFiniteKPProjectiveBorel K hζ Q) P

local notation "ιₛ" => sourceKPAdelicOutgoingLocalGroupTuple K hζ P
local notation "ιᴮ" => sourceKPAdelicOutgoingLocalBorelTuple K hζ P

theorem sourceKPAdelicOutgoingLocalGroupTuple_surjective : Function.Surjective ιₛ := by
  intro g
  refine ⟨g p₀, ?_⟩
  funext Q
  have hQ : Q = p₀ := Subtype.ext (Finset.mem_singleton.mp Q.property)
  subst Q
  exact Pi.mulSingle_eq_same (M := LocalGroup) p₀ (g p₀)

theorem sourceKPAdelicOutgoingLocalBorelTuple_val (b : B₀) :
    (fun Q : ↥S => (ιᴮ b Q).val) = ιₛ b.val := by
  funext Q
  have hQ : Q = p₀ := Subtype.ext (Finset.mem_singleton.mp Q.property)
  subst Q
  change (Pi.mulSingle (M := LocalBorel) p₀ b p₀).val =
    Pi.mulSingle (M := LocalGroup) p₀ b.val p₀
  exact (congrArg (fun y : B₀ => y.val)
    (Pi.mulSingle_eq_same (M := LocalBorel) p₀ b)).trans
    (Pi.mulSingle_eq_same (M := LocalGroup) p₀ b.val).symm

theorem sourceKPAdelicOutgoingLocalGroupTuple_lift (g : G₀) : L (ιₛ g) = ι₀ g := by
  unfold sourceKPLocalCompactProductLift sourceKPAdelicOutgoingLocalGroupTuple
  exact sourceKPOutgoingSingletonTuple_lift (fun Q => SourceFiniteKP2Projective K hζ Q)
    (sourceKPAdelicLocalProjective K hζ) P g

theorem sourceKPAdelicOutgoingLocalBorelTuple_lift (b : B₀) :
    sourceKPLocalCompactProductBorelLift K hζ S (ιᴮ b) =
      sourceKPAdelicLocalBorel K hζ P b := by
  unfold sourceKPLocalCompactProductBorelLift sourceKPAdelicOutgoingLocalBorelTuple
  exact sourceKPOutgoingSingletonTuple_lift (fun Q => SourceFiniteKPProjectiveBorel K hζ Q)
    (sourceKPAdelicLocalBorel K hζ) P b

local instance sourceKPAdelicOutgoingLocalReceiverTorusAddCommGroup (s : ℂ) :
    AddCommGroup (V s) := Submodule.addCommGroup _

local instance sourceKPAdelicOutgoingLocalReceiverCarrierAddCommGroup (s : ℂ) (hs : 0 < s.re) :
    AddCommGroup (W s hs) := Submodule.addCommGroup _

def sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation (s : ℂ) (hs : 0 < s.re) :
    Representation ℂ B₀ (W s hs) :=
  (sourceKPAdelicOutgoingRegularizedRetainedBorelRepresentation K hζ S s hs).comp ιᴮ

local notation "ρ₀" => sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation K hζ P

theorem sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_apply (s : ℂ) (hs : 0 < s.re)
    (b : B₀) (v : W s hs) (r : Rest) :
    (ρ₀ s hs b v).val r = sourceKPAdelicLocalBorelRepresentation K hζ P (-s) b (v.val r) := by
  change sourceKPAdelicNormalizedBorelRepresentation K hζ (-s)
      (sourceKPLocalCompactProductBorelLift K hζ S (ιᴮ b)) (v.val r) =
    sourceKPAdelicNormalizedBorelRepresentation K hζ (-s) (sourceKPAdelicLocalBorel K hζ P b) (v.val r)
  rw [sourceKPAdelicOutgoingLocalBorelTuple_lift K hζ P]

theorem sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_upper (s : ℂ) (hs : 0 < s.re)
    (x : P.adicCompletion K) (v : W s hs) :
    ρ₀ s hs (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v := by
  apply Subtype.ext
  funext r
  rw [sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_apply K hζ P]
  exact sourceKPAdelicLocalBorelRepresentation_upper K hζ P (-s) x (v.val r)

theorem sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_cube (s : ℂ) (hs : 0 < s.re)
    (u : (P.adicCompletion K)ˣ) (v : W s hs) :
    ρ₀ s hs (sourceFiniteKPProjectiveBorelDiagonal K hζ P (u^3)) v =
      (sourceKPIdeleComplexNorm K (-s+1/2) ((IdeleGroup.ofAdicCompletion (𝓞 K) K P u)^3) : ℂ) • v := by
  apply Subtype.ext
  funext r
  rw [sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_apply K hζ P]
  exact sourceKPAdelicLocalBorelRepresentation_cube K hζ P (-s) u (v.val r)

theorem sourceKPAdelicOutgoingExceptionalLocalBorelRepresentation_cube (hs : 0 < (1 / 6 : ℂ).re)
    (u : (P.adicCompletion K)ˣ) (v : W (1 / 6) hs) :
    ρ₀ (1 / 6) hs (sourceFiniteKPProjectiveBorelDiagonal K hζ P (u^3)) v =
      ((‖((u^3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)‖ ^ (1 / 3 : ℝ) : ℝ) : ℂ) • v := by
  have hangle : -(1 / 6 : ℂ) + 1 / 2 = ((1 / 3 : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_div]
  rw [sourceKPAdelicOutgoingRegularizedLocalBorelRepresentation_cube K hζ P,
    ← map_pow (IdeleGroup.ofAdicCompletion (𝓞 K) K P), hangle, sourceKPIdeleComplexNorm_real,
    sourceKPIdeleAbsoluteNorm_ofAdicCompletion]

def sourceKPAdelicOutgoingRegularizedLocalSection (s : ℂ) (hs : 0 < s.re) :
    sourceKPLocalCompactFixedSpace K hζ P (ρ₀ s hs) := by
  let v := sourceKPAdelicOutgoingRegularizedRetainedVector K hζ S s hs
  refine ⟨⟨fun g => v (ιₛ g), ?_⟩, ?_⟩
  · intro b g
    change v (ιₛ (b.val*g)) =
      sourceKPAdelicOutgoingRegularizedRetainedBorelRepresentation K hζ S s hs (ιᴮ b) (v (ιₛ g))
    rw [map_mul ιₛ, ← sourceKPAdelicOutgoingLocalBorelTuple_val K hζ P b]
    exact sourceKPAdelicOutgoingRegularizedRetainedVector_borel K hζ S s hs (ιᴮ b) (ιₛ g)
  · intro g j
    apply Subtype.ext
    funext r
    change (R s hs).val (L (ιₛ (g*j.val.val))*r.val) = (R s hs).val (L (ιₛ g)*r.val)
    rw [sourceKPAdelicOutgoingLocalGroupTuple_lift K hζ P,
      sourceKPAdelicOutgoingLocalGroupTuple_lift K hζ P]
    have hmem := sourceKPLocalCompactDeepCoverLevel_global_mem K hζ P
      (show j.val.val ∈ J₀ from ⟨j.val,j.property,rfl⟩)
    let k : D := ⟨ι₀ j.val.val,hmem⟩
    have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P j.val.val r.val (r.property p₀)
    rw [map_mul ι₀,mul_assoc,hc.eq,← mul_assoc]
    exact congrArg (fun f : Vₚ (-s) => f.val (ι₀ g*r.val))
      (sourceKPAdelicOutgoingRegularizedSection_right K hζ s hs k)

local notation "R₀" => sourceKPAdelicOutgoingRegularizedLocalSection K hζ P

theorem sourceKPAdelicOutgoingRegularizedLocalSection_apply (s : ℂ) (hs : 0 < s.re)
    (g : G₀) (r : Rest) :
    ((R₀ s hs).val.val g).val r = (R s hs).val (ι₀ g*r.val) := by
  change (R s hs).val (L (ιₛ g)*r.val) = _
  rw [sourceKPAdelicOutgoingLocalGroupTuple_lift K hζ P]

theorem sourceKPAdelicOutgoingRegularizedLocalCarrier_finiteDimensional (s : ℂ) (hs : 0 < s.re) :
    FiniteDimensional ℂ (W s hs) :=
  sourceKPAdelicOutgoingRegularizedRetainedCarrier_finiteDimensional K hζ S s hs

theorem sourceKPAdelicOutgoingRegularizedLocalFixed_finiteDimensional (s : ℂ) (hs : 0 < s.re) :
    FiniteDimensional ℂ (sourceKPLocalCompactFixedSpace K hζ P (ρ₀ s hs)) := by
  let : FiniteDimensional ℂ (W s hs) :=
    sourceKPAdelicOutgoingRegularizedLocalCarrier_finiteDimensional K hζ P s hs
  exact sourceKPLocalCompactFixedSpace_finiteDimensional K hζ P (ρ₀ s hs)

end
end ArtinMatthews

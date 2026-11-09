module

public import ArtinMatthews.SourceKPPhysicalHorizontal
public import ArtinMatthews.SourceKPRetainedPrincipalTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The signed reflected finite fiber has a literal word in canonical
cover lifts, with its original reflection phase outside that word. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "Z" => sourceKPFiniteAdeleProjectiveCenter K hζ
local notation "Nf" => sourceKPFiniteAdeleUpperLift K hζ
local notation "R" => sourceKPAdelicProjectiveRationalLift K hζ
local notation "D" => sourceKPDiagonalHom 𝔸ᶠ[K]
local notation "f" => sourceKPIdeleFiniteUnit K
local notation "rat" => FiniteAdeleRing.unitEmbedding (𝓞 K) K
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "σ" => sourceKPTraceJacquetFrequencyAt K
local notation "L" => sourceFiniteKP2Lift K hζ
local notation "U" => sourceKPUpperMatrix 𝔸ᶠ[K]

def sourceKPReflectedRetainedUpper (S : Finset Pr) (v : ∀ P : S, P.val.adicCompletion K) : 𝔸ᶠ[K] :=
  ∑ P : S, sourceKPFiniteAdditiveSingle K P.val (v P)

theorem sourceKPReflectedRetainedUpper_at (S : Finset Pr) (v : ∀ P : S, P.val.adicCompletion K)
    (P : S) : sourceKPReflectedRetainedUpper K S v P.val = v P := by
  change sourceKPAdeleEval K P.val (∑ Q : S, sourceKPFiniteAdditiveSingle K Q.val (v Q)) = _
  rw [map_sum, Finset.sum_eq_single_of_mem P (Finset.mem_univ P)]
  · exact sourceKPFiniteAdditiveSingle_same K P.val (v P)
  · intro Q _ hQ
    exact sourceKPFiniteAdditiveSingle_other K Q.val (v Q) P.val (fun h => hQ (Subtype.ext h.symm))

def sourceKPReflectedFiniteMatrices (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) : List A :=
  [D (rat m), D (f (sourceSLocalExteriorIdele K S ((b⁻¹)^2))),
    D (f (sourceSLocalIdeleLift K S x)), D (rat (-1)), sourceKPWeylMatrix 𝔸ᶠ[K],
    U u, U (sourceKPReflectedRetainedUpper K S v)]

def sourceKPReflectedFiniteCover (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) : F :=
  ((sourceKPReflectedFiniteMatrices K S m b x u v).map (fun g => (⟨1,g⟩ : F))).prod *
    sourceKPAdelicRootSupportProduct K hζ a₀ S

def sourceKPReflectedFiniteLocalWord (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) (P : Pr) :
    SourceFiniteKP2Cover K hζ P :=
  ((sourceKPReflectedFiniteMatrices K S m b x u v).map (fun g => L P (ev P g))).prod *
    (if P ∈ S then L P (ev P a₀) else 1)

theorem sourceKPReflectedFiniteCover_mk (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A) :
    sourceKPCuspResidualUnitTranslate K hζ m
      (sourceKPReflectedHorizontalFiber K hζ S b
        (Nf u * (Nf (sourceKPReflectedRetainedUpper K S v) * (sourceKPAdelicRootSupportTuple K hζ 1 a₀ S).2)) x) =
      Z (sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)) *
        M (sourceKPReflectedFiniteCover K hζ S m b x u v a₀) := by
  let a := fun g : A => (⟨1,g⟩ : F)
  have hrat (t : Kˣ) : (R (sourceKPProjectiveDiagonalHom K t)).2 = M (a (D (rat t))) :=
    sourceKPFiniteAdeleProjectiveRationalLift_diagonal K hζ t
  have hW : (R (ProjGenLinGroup.mk (sourceKPWeylMatrix K))).2 = M (a (sourceKPWeylMatrix 𝔸ᶠ[K])) :=
    sourceKPFiniteAdeleProjectiveRationalLift_weyl K hζ
  have hsign : (R (sourceKPReflectionWeyl K 1)).2 =
      M (a (D (rat (-1)))) * M (a (sourceKPWeylMatrix 𝔸ᶠ[K])) := by
    rw [sourceKPReflectionWeyl_eq]
    simp only [inv_one, one_pow, map_one, one_mul, map_mul, Prod.snd_mul, hrat, hW]
  let z := sourceSLocalWeylPhase K S hζ b (sourceKPSLocalReflectionArgument K S b*x⁻¹)
  rw [sourceKPCuspResidualUnitTranslate, sourceKPReflectedHorizontalFiber, hrat, hsign]
  change M (a (D (rat m))) *
    (Z z * M (a (D (f (sourceSLocalExteriorIdele K S ((b⁻¹)^2))))) *
      M (a (D (f (sourceSLocalIdeleLift K S x)))) *
      (M (a (D (rat (-1)))) * M (a (sourceKPWeylMatrix 𝔸ᶠ[K]))) *
      (M (a (U u)) * (M (a (U (sourceKPReflectedRetainedUpper K S v))) *
        M (sourceKPAdelicRootSupportProduct K hζ a₀ S)))) = _
  simp only [sourceKPReflectedFiniteCover, sourceKPReflectedFiniteMatrices, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul, mul_assoc]
  exact (sourceKPFiniteAdeleProjectiveCenter_commute K hζ z (M (a (D (rat m))))).symm.left_comm _

theorem sourceKPReflectedFiniteLocalWord_retained (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A)
    (P : S) (hu : u P.val = 0) :
    sourceKPReflectedFiniteLocalWord K hζ S m b x u v a₀ P.val =
      L P.val (sourceGL2Diagonal (σ P.val m)) * L P.val (sourceGL2Diagonal (x.2 P)) *
        (L P.val (sourceGL2Diagonal (-1)) * L P.val sourceGL2Weyl) *
        L P.val (sourceGL2Upper (v P)) * L P.val (ev P.val a₀) := by
  have hm (t : Kˣ) : ev P.val (D (rat t)) = sourceGL2Diagonal (σ P.val t) := by
    rw [sourceKPAdeleMatrixAt_diagonal]
    exact congrArg sourceGL2Diagonal (sourceKPRetainedUnitAt_rational K P.val t)
  have hb : ev P.val (D (f (sourceSLocalExteriorIdele K S ((b⁻¹)^2)))) = 1 := by
    rw [sourceKPAdeleMatrixAt_diagonal]
    change sourceGL2Diagonal (sourceKPIdeleFiniteCoordinate K P.val (sourceSLocalExteriorIdele K S ((b⁻¹)^2))) = 1
    rw [sourceSLocalExteriorIdele_finite_in, ← sourceKPDiagonalHom_field, map_one]
  have hx : ev P.val (D (f (sourceSLocalIdeleLift K S x))) = sourceGL2Diagonal (x.2 P) := by
    rw [sourceKPAdeleMatrixAt_diagonal]
    exact congrArg sourceGL2Diagonal (sourceSLocalIdeleLift_finite_in K S x P)
  have hs : σ P.val (-1) = -1 := by
    apply Units.ext
    change algebraMap K (P.val.adicCompletion K) (-1) = -1
    simp
  simp only [sourceKPReflectedFiniteLocalWord, sourceKPReflectedFiniteMatrices, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, hm, hb, hx, sourceKPAdeleMatrixAt_weyl,
    sourceKPAdeleMatrixAt_upper, hu, sourceKPReflectedRetainedUpper_at,
    sourceGL2Upper_zero, ite_eq_left P.property, hs, mul_assoc, mul_one,
    show L P.val (1 : GL (Fin 2) (P.val.adicCompletion K)) = 1 from rfl, one_mul]

theorem sourceKPReflectedExteriorDiagonal_at (S : Finset Pr) (b : Kˣ) (P : Pr) (hP : P ∉ S) :
    ev P (D (f (sourceSLocalExteriorIdele K S ((b⁻¹)^2)))) = sourceGL2Diagonal (((σ P b)⁻¹)^2) := by
  let e := Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom
  let i := IdeleGroup.unitEmbedding (𝓞 K) K
  have hσ (t : Kˣ) : sourceKPIdeleFiniteCoordinate K P (i t) = e t := Units.ext rfl
  rw [sourceKPAdeleMatrixAt_diagonal]
  change sourceGL2Diagonal (sourceKPIdeleFiniteCoordinate K P (sourceSLocalExteriorIdele K S ((b⁻¹)^2))) = _
  rw [sourceSLocalExteriorIdele_finite_out K S _ P hP, hσ, map_pow, map_inv]
  rfl

theorem sourceKPReflectedRetainedDiagonal_at_exterior (S : Finset Pr) (x : SWholeUnits K S)
    (P : Pr) (hP : P ∉ S) : ev P (D (f (sourceSLocalIdeleLift K S x))) = 1 := by
  rw [sourceKPAdeleMatrixAt_diagonal]
  change sourceGL2Diagonal (sourceKPIdeleFiniteCoordinate K P (sourceSLocalIdeleLift K S x)) = 1
  rw [sourceSLocalIdeleLift_finite_out K S x P hP, ← sourceKPDiagonalHom_field, map_one]

theorem sourceKPReflectedFiniteLocalWord_exterior (S : Finset Pr) (m b : Kˣ) (x : SWholeUnits K S)
    (u : 𝔸ᶠ[K]) (v : ∀ P : S, P.val.adicCompletion K) (a₀ : A)
    (P : Pr) (hP : P ∉ S) :
    sourceKPReflectedFiniteLocalWord K hζ S m b x u v a₀ P =
      L P (sourceGL2Diagonal (σ P m)) * L P (sourceGL2Diagonal (((σ P b)⁻¹)^2)) *
        (L P (sourceGL2Diagonal (-1)) * L P sourceGL2Weyl) * L P (sourceGL2Upper (u P)) := by
  have hm (t : Kˣ) : ev P (D (rat t)) = sourceGL2Diagonal (σ P t) := by
    rw [sourceKPAdeleMatrixAt_diagonal]
    exact congrArg sourceGL2Diagonal (sourceKPRetainedUnitAt_rational K P t)
  have hb := sourceKPReflectedExteriorDiagonal_at K S b P hP
  have hx := sourceKPReflectedRetainedDiagonal_at_exterior K S x P hP
  have hv : sourceKPReflectedRetainedUpper K S v P = 0 := sourceKPRetainedUpperSum_apply_notMem K S v P hP
  have hs : σ P (-1) = -1 := by
    apply Units.ext
    change algebraMap K (P.adicCompletion K) (-1) = -1
    simp
  simp only [sourceKPReflectedFiniteLocalWord, sourceKPReflectedFiniteMatrices, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, hm, hb, hx, sourceKPAdeleMatrixAt_weyl,
    sourceKPAdeleMatrixAt_upper, hv, sourceGL2Upper_zero, ite_eq_right hP, hs, mul_assoc, mul_one,
    show L P (1 : GL (Fin 2) (P.adicCompletion K)) = 1 from rfl, one_mul]

end
end ArtinMatthews

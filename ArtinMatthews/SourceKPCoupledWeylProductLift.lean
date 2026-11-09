module

public import ArtinMatthews.SourceKPCoupledWeylMatrices


set_option backward.privateInPublic true
@[expose] public section

/-! The finite Weyl word has its literal phase-one matrix lift, with
each place appearing exactly when it is in the selected finite set. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceKPCoupledSingleWeyl_commute :
    Pairwise (fun P Q : S => Commute (sourceKPCoupledSingleWeylMatrix K P.val)
      (sourceKPCoupledSingleWeylMatrix K Q.val)) := by
  intro P Q hPQ
  apply Subtype.ext
  exact (sourceKPAdeleSingleMatrix_commute K P.val Q.val
    (fun h => hPQ (Subtype.ext h.symm)) _ _).eq

def sourceKPCoupledWeylMatrixProduct : sourceKPCoupledWeylMatrices K :=
  Finset.univ.noncommProd (fun P : S => sourceKPCoupledSingleWeylMatrix K P.val)
    (fun _ _ _ _ h => sourceKPCoupledSingleWeyl_commute K S h)

set_option backward.isDefEq.respectTransparency false in
theorem sourceKPCoupledWeylMatrixProduct_at (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdeleMatrixAt K P (sourceKPCoupledWeylMatrixProduct K S).val =
      if P ∈ S then sourceGL2Weyl else 1 := by
  let e := (sourceKPAdeleMatrixAt K P).comp (sourceKPCoupledWeylMatrices K).subtype
  change e (sourceKPCoupledWeylMatrixProduct K S) = _
  have he := Finset.map_noncommProd (Finset.univ : Finset S)
    (fun Q : S => sourceKPCoupledSingleWeylMatrix K Q.val)
    (fun _ _ _ _ h => sourceKPCoupledSingleWeyl_commute K S h) e
  change e (sourceKPCoupledWeylMatrixProduct K S) = _ at he
  rw [he]
  by_cases hP : P ∈ S
  · rw [ite_eq_left hP]
    let p : S := ⟨P,hP⟩
    rw [← Finset.insert_erase (Finset.mem_univ p), Finset.noncommProd_insert_of_notMem _ _ _ _ (Finset.notMem_erase p _)]
    rw [Finset.noncommProd_eq_pow_card _ _ _ (1 : GL (Fin 2) (P.adicCompletion K))]
    · rw [one_pow, mul_one]
      exact sourceKPAdeleSingleMatrix_same K P _
    · intro Q hQ
      change sourceKPAdeleMatrixAt K P (sourceKPAdeleSingleMatrix K Q.val sourceGL2Weyl) = 1
      exact sourceKPAdeleSingleMatrix_other K Q.val P
        (fun h => (Finset.mem_erase.mp hQ).1 (Subtype.ext h.symm)) _
  · rw [ite_eq_right hP, Finset.noncommProd_eq_pow_card _ _ _ (1 : GL (Fin 2) (P.adicCompletion K))]
    · exact one_pow _
    · intro Q _
      change sourceKPAdeleMatrixAt K P (sourceKPAdeleSingleMatrix K Q.val sourceGL2Weyl) = 1
      exact sourceKPAdeleSingleMatrix_other K Q.val P (fun h => hP (h ▸ Q.property)) _

set_option backward.isDefEq.respectTransparency false in
theorem sourceKPCoupledWeylMatrixProduct_lift :
    sourceKPCoupledWeylMatrixLift K hζ (sourceKPCoupledWeylMatrixProduct K S) =
      (sourceKPCoupledLocalProduct K hζ S
        (fun P => sourceFiniteKP2ProjectiveLift K hζ P.val sourceGL2Weyl)).2 := by
  have he := Finset.map_noncommProd (Finset.univ : Finset S)
    (fun Q : S => sourceKPCoupledSingleWeylMatrix K Q.val)
    (fun _ _ _ _ h => sourceKPCoupledSingleWeyl_commute K S h) (sourceKPCoupledWeylMatrixLift K hζ)
  change sourceKPCoupledWeylMatrixLift K hζ (sourceKPCoupledWeylMatrixProduct K S) = _ at he
  let p := MonoidHom.snd (PGL(2, InfiniteAdeleRing K)) (SourceKPFiniteAdeleProjective K hζ)
  let f := fun P : S => sourceFiniteKP2ProjectiveLift K hζ P.val sourceGL2Weyl
  let g := fun P : S => sourceKPAdelicLocalProjective K hζ P.val (f P)
  have hg : ((Finset.univ : Finset S) : Set S).Pairwise (fun P Q => Commute (g P) (g Q)) := by
    intro P _ Q _ hPQ
    exact sourceKPAdelicLocalProjective_commute K hζ P.val Q.val
      (fun h => hPQ (Subtype.ext h.symm)) _ _
  change _ = p ((Finset.univ : Finset S).noncommProd g hg)
  refine he.trans ?_
  refine (Finset.noncommProd_congr rfl (g := fun P => p (g P)) ?_ _).trans
    (Finset.map_noncommProd Finset.univ g hg p).symm
  intro P _
  exact sourceKPCoupledSingleWeylMatrix_lift K hζ P.val

theorem sourceKPCoupledWildWeyl_lift :
    (sourceKPCoupledWildWeyl K hζ).2 =
      sourceKPFiniteAdeleProjectiveLift K hζ
        (sourceKPCoupledWeylMatrixProduct K (sixthWildPrimes K)).val :=
  (sourceKPCoupledWeylMatrixProduct_lift K hζ (sixthWildPrimes K)).symm

end
end ArtinMatthews

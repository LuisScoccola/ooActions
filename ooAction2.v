(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.
Import TrM.


Context (G : ooGroup).
Local Notation B := classifying_space.

Section SomeLemmas.

  (* given a fibration [A : T -> U] and a dependent fibration [B (t : T) : (a : T a) -> U]
     we can form a product fibration [AxB t := { y : A t  &  B t y }].
     The lemma is that given a path [p] in [T] it is the same:
     [(transport AxB p x).1] and [transport A p x.1]
  *)
  Definition product_fibration
             {T : Type}
             (A : T -> Type) (B : forall (t : T) (a : A t), Type)
             : T -> Type
  := fun t => { y : A t & B t y}.
  
  Definition transport_on_first_coordinate
             {T : Type} (A : T -> Type) (B : forall (t : T) (a : A t), Type)
             {t1 t2 : T} (p : t1 = t2) (x : product_fibration A B t1)
             : (transport (product_fibration A B) p x).1 =
                 transport A p x.1.
  Proof.
    by induction p.
  Defined.
  
  (* a connected type is merely inhabited.
     I don't think this is done explicitly in the library
     although this argument is taken from the proof
     of [indecomposable_0connected] *)
  Definition isinhabitedifisconnected
             (A : Type)
             : IsConnected 0 A -> merely A.
  Proof.
    intro cc.
    assert (IsConnected -1 A) by refine (isconnected_pred -1 A).
    pose (mA := center (merely A)).
    exact mA.
  Defined.
  
  
  (* a (forall) product of mere propositions is a mere proposition.
     could not find this in the library *)
  Definition ishprop_productofhprop `{Funext}
             {A : Type} (P : A -> Type) (D : forall a, IsHProp (P a))
             : IsHProp (forall a, P a).
  Proof.
    refine (hprop_allpath _ _).
    intros f g.
    refine (path_forall _ _ _).
    intro a.
    apply (D a).
  Defined.

  (* a (binary) product of mere propositions is a mere proposition. *)
   Definition ishprop_bi_productofhprop `{Funext}
              {A B : Type} (pA : IsHProp A) (pB : IsHProp B)
              : IsHProp (A * B).
   Proof.
     refine (@trunc_prod (-1) A pA B pB ).
   Defined.

End SomeLemmas.


Section BasicDefinitions.

  (* non-empty action *)
  Definition isNonempty (A : ooAction G) : Type
  := merely (action_space A).
  
  (* transitive action *)
  Definition isTransitive (A : ooAction G) : Type
  := IsConnected 0 (sigT A).
  
  (* alternative def transitive action *)
  Definition isTransitive' (A : ooAction G) : Type
  := (isNonempty A) * 
       (forall x y : A, merely {g : G & g # x = y}).
  

  (* free action *)
  Definition isFree (A : ooAction G) : Type
  := IsTrunc 1 (sigT A).

  (* alternative def free action *)
  Definition isFree' (A : ooAction G) : Type
  := forall a : A, Contr {g : G & g # a = a}.
  

  (* regular action *)
  Definition isRegular (A : ooAction G) : Type
  := (isTransitive A) * (isFree A).
  
  (* alternative def regular action *)
  Definition isRegular' (A : ooAction G) : Type
  := Contr (sigT A).
  
End BasicDefinitions.
  

Section ProofsAboutDefinitions.

  (* a transitive action is non-empty *)
  Definition isnonempty_transitiveaction `{Univalence}
             (A : ooAction G)
             : isTransitive A -> isNonempty A.
  Proof.
    intro.
    unfold isNonempty. simpl.
    cut (Trunc (-1) (sigT A)).
    intros mSA.
    strip_truncations.
    cut (Trunc (-1) ((point (B G)) = mSA.1)).
    refine (Trunc_functor _ _).
      - intro p. exact (transport _ p^ (pr2 mSA)).
      - exact (merely_path_is0connected _ (point (B G)) (pr1 mSA)).
      - exact (isinhabitedifisconnected _ X).
  Defined.
  

 (** both definitions of transitive action are equivalent.
     we prove that both are mere propositions and that they
     are logically equivalent  *)
  
  (* being transitive is a mere property *)
  Definition ishProp_isTransitive `{Funext}
             (A : ooAction G)
             : IsHProp (isTransitive A)
  := ishprop_isconnected _ _.
  
  (* being transitive' is a mere property *)
  Definition ishProp_isTransitive' `{Funext}
             (A : ooAction G)
             : IsHProp (isTransitive' A).
  Proof.
    unfold isTransitive'.
    exact (ishprop_bi_productofhprop _ _).
  Defined.

  
  Definition transitive2transitive' `{Univalence}
             (A : ooAction G)
             : isTransitive A -> isTransitive' A.
  Proof.
    intro. unfold isTransitive'.
    refine ((isnonempty_transitiveaction A X) , _).
    intros x y.
    pose (mereg := @merely_path_is0connected _ _ X ((point (B G)) ; x)
                                                   ((point (B G)) ; y)).
    (* the following command takes some seconds *)
    simpl in mereg. simpl.
    cut (Trunc (-1) ((point (B G); x) = (point (B G); y))).
    refine (Trunc_functor _ _).
      - intro p. exact (p..1 ; p..2).
      - exact mereg.
  Defined.
  
  Definition transitive'2transitive `{Univalence}
             (A : ooAction G)
             : isTransitive' A -> isTransitive A.
  Proof.
    intro tr'. unfold isTransitive' in tr'.
    refine (is0connected_merely_allpath _ _).
      - cut (Trunc (-1) A).
          + intro mA. strip_truncations. exact (tr (point (B G) ; mA)).
          + exact (fst tr').
      - intros x y.
        pose (mp := snd tr').
        pose (mpx := @merely_path_is0connected _ _ _ (point (B G)) (pr1 x)).
        pose (mpy := @merely_path_is0connected _ _ _ (point (B G)) (pr1 y)).
        (* there is probably a more elegant way to do this. maybe
           strip_truncations or something similar should work here? *)
        generalize mpx, mpy.
        refine (Trunc_rec _).
        intro px.
        refine (Trunc_rec _).
        intro py.
        (* transport [x] and [y] to [A], and rememeber the paths used *)
        pose (tx := transport _ px^ (pr2 x)).
        pose (xetx := path_sigma _ x ((point (B G)) ; tx) px^ 1).
        pose (ty := transport _ py^ (pr2 y)).
        pose (yety := path_sigma _ y ((point (B G)) ; ty) py^ 1).
        pose (txety'' := mp tx ty).
        (* the transported [x] and [y] are equal in [A] *)
        generalize txety''.
        refine (Trunc_rec _).
        intro txety'.
        pose (txety := path_sigma _ ((point (B G)) ; tx)
                                    ((point (B G)) ; ty)
                                    (pr1 txety') (pr2 txety')).
        (* finally compose the equalities *)
        exact (tr (xetx @ txety @ yety^)).
  Defined.

End ProofsAboutDefinitions.
  

Section MoreDefinitions.
  (* orbit action: given an action [X] and a point [x] we can
     consider the orbit of this point. There is an
     action [orbit_action] that is the restriction of the action
     on [X] to the the orbit of [x] *)
  Definition orbit_action
             (X : ooAction G) (x : action_space X)
             : ooAction G
  := fun b => { y : X(b) &
                merely ((point (B G) ; x) = (b ; y)) }.
  
  
  
  (* stabilizer: defined as the connected component of
     [(point (B G)) ; x)] in [sigT A]

     todo: use [group_loops]
  *)
  Definition stabilizer
             (X : ooAction G) (x : action_space X)
             : ooGroup.
  Proof.
    pose (Ox := Build_pType (sigT (orbit_action X x))
                            ( (point (B G)) ; (x ; tr idpath ) ) ).
    refine (Build_ooGroup Ox _).
    (* this is how Mike does it in ooGroup.v *)
    cut (IsSurjection (unit_name (point Ox))).
    { intros; refine (conn_pointed_type (point _)). }
    apply BuildIsSurjection; simpl; intros [b ty].
    destruct ty as (y, p).
    strip_truncations. apply tr. exists tt.
    simple refine (path_sigma _ _ _ _ _).
      - exact (p ..1).
      - apply path_sigma_hprop. simpl.
        refine ((transport_on_first_coordinate _ _ _ _) @ _).
        exact (p ..2).
  Defined.
 
  (* map from stabilizer to group *)
  Definition stabilizer_to_G (X : ooAction G) (x : action_space X) :
               ooGroupHom (stabilizer X x) G.
  Proof.  
    simple refine (Build_pMap _ _ _ _).
      - exact pr1.
      - reflexivity.
  Defined.
  
  
  (* how it computes on paths *)
  Definition stabilizer_to_G_path
             (X : ooAction G) (x : action_space X) (l : stabilizer X x)
             : (stabilizer_to_G X x) l = l ..1.
  Proof.
    unfold stabilizer_to_G. unfold grouphom_fun. unfold loops_functor. simpl.
    refine (concat_1p _ @ _). refine (concat_p1 _ @ _).
    reflexivity.
  Defined.
  
  
  (* the stabilizer of [x] acts trivially on [x] *)
  Definition stab_acts_trivially
             {X : ooAction G} {x : action_space X} (l : stabilizer X x)
             : transport X ((stabilizer_to_G X x) l) x = x.
  Proof.
    pose (pr1l2 := pr1_path l..2).
    pose (pr := (transport_on_first_coordinate _ _ _ _)^ @ pr1l2).
    simpl in pr.
    refine (ap (fun path => transport X path x)
               (stabilizer_to_G_path _ _ l) @ _).
    apply pr.
  Defined.
  
  
  (* relation of being in the same coset *)
  Definition in_coset_morph
             {H : ooGroup} (f : ooGroupHom H G) (b : B G)
             : (point (B G)) = b -> (point (B G)) = b -> Type
    := fun g1 g2 => hfiber f (g1 @ g2^).
  
  
  (* quotient given by coset relation *)
  Definition reltocoeq {A : Type} (R : A -> A -> Type) : Type
  := @Coeq {p : A * A & R (fst p) (snd p)} A (fst o pr1) (snd o pr1).
  
  
  (* action on cosets *)
  Definition action_cosets
             {H : ooGroup} (f : ooGroupHom H G)
             : ooAction G
  := fun b => reltocoeq (in_coset_morph f b).
  
  
  (* fiberwise map cosets action to orbit action *)
  Definition cosets_to_orbit
             {X : ooAction G} {x : action_space X} (b : B G)
             : (action_cosets (stabilizer_to_G X x) b) -> orbit_action X x b.
  Proof.
    simple refine (Coeq_rec _ _ _).
      - intro p. exists (p # x).
        apply tr. simple refine (path_sigma _ _ _ _ _).
          + simpl. exact p.
          + reflexivity.
      - intros. simpl.
        simple refine (path_sigma _ _ _ _ _).
          + simpl. induction b0 as (p, pp).
            apply moveL_transport_p. rewrite <- transport_pp.
            induction pp as (l, t).
            refine ( (ap (fun e => transport X e x) t^) @ _ ).
            pose (l1 := l ..1).
            pose (l2 := l ..2).
            pose (l21 := ap pr1 l2).
            pose (pr := (transport_on_first_coordinate _ _ _ _)^ @ l21).
            simpl in pr.

            refine (ap (fun path => transport X path x)
                       (stabilizer_to_G_path _ _ l) @ _).
            apply pr.
          + apply path_ishprop.
  Defined.
  
  (* this is probably false but it seems to be true for
     subgroups (i.e. when the map [B H -> B G] is fibered in set)
  (* this map is an equivalence *)
  Definition isequiv_cosets_to_orbit
               {X : ooAction G} {x : action_space X} (b : B G) :
                 IsEquiv (@cosets_to_orbit X x b).
  Proof.
  *)
  
End MoreDefinitions.


Section More.

(* other *)
  (* stabilizer: *)
  Definition stabilizer'
             (X : ooAction G) (x : action_space X)
             : ooGroup
  := group_loops (Build_pType (sigT (orbit_action X x))
                              ( (point (B G)) ; (x ; tr idpath ) ) ).
  
  (* map from stabilizer' to group *)
  Definition stabilizer'_to_G
             (X : ooAction G) (x : action_space X)
             : ooGroupHom (stabilizer' X x) G.
  Proof.
    simple refine (Build_pMap _ _ _ _).
      - intro bb.
        exact (pr1 (pr1 bb)).
      - reflexivity.
  Defined.

End More.
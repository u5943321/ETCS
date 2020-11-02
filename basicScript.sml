Theorem po_with_one:
∀A. po A one ≅ A
Proof
rw[are_iso_def] >> qexistsl_tac [‘p1 A one’,‘⟨id A,to_terminal A⟩’]>>
rw[] >> cheat
QED

Theorem ev_of_tp:
∀A B X f. f∶A × X → B ⇒ ev A B ∘ ⟨p1 A X, tp f ∘ p2 A X⟩ = f
Proof
metis_tac[ax2]
QED

Theorem tp_hom:
∀A B C f. f∶ A× B → C ⇒ tp f∶ B → exp A C
Proof
metis_tac[ax2]        
QED

Theorem tp_eq:
∀A B C f g. f∶ A×B → C ∧ g∶ A×B → C ⇒ (tp f = tp g ⇔ f = g)
Proof
rw[] >> metis_tac[ev_of_tp]
QED

 
Theorem is_tp:
∀A B X f h. f∶ A × X → B ∧ h∶ X → exp A B ∧
            (ev A B) o ⟨p1 A X, h o (p2 A X)⟩ = f ⇒
            h = tp f
Proof
metis_tac[ax2]
QED

(*‘⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ =
   ⟨p1 A N, (tp f) o (p2 A N)⟩ o ⟨p1 A N, s o (p2 A N)⟩’*)        


Theorem ax2_conj2:
∀A B X f. f∶ (po A X) → B ⇒
          (∀h. (h∶ X → (exp A B) ∧
                (ev A B) o (pa (p1 A X) (h o (p2 A X))) = f) ⇔
                 h = tp f)
Proof
metis_tac[ax2]
QED                                  


Theorem ax3_conj2:
∀X x0 t. x0∶ one → X ∧ t∶ X → X ⇒
                     !x. (x∶ N → X ∧ x o z = x0 ∧ x o s = t o x) ⇔
                         x = N_ind x0 t
Proof
metis_tac[ax3]
QED
                                                              
Theorem pa_hom:
∀A B X f g. f∶ X→ A ∧ g∶ X→ B ⇒ ⟨f,g⟩∶ X → (A×B)
Proof
metis_tac[ax1_3]
QED
                                     
Theorem ev_hom:
∀A B. ev A B∶ (A× (exp A B))→ B
Proof
metis_tac[ax2]
QED

                                     
Theorem ev_of_pair_hom:
∀A B X f. f∶ X → (exp A B) ⇒ (ev A B) o ⟨p1 A X,f o (p2 A X)⟩∶ (A×X) → B
Proof
rw[] >>
irule compose_hom >> qexists_tac ‘(po A (exp A B))’ >>
rw[] (* 2 *)
>- (irule pa_hom >> metis_tac[ax1_3,compose_hom])
>- metis_tac[ax2]
QED
                                             
Theorem ev_eq_eq:
∀A B X f g. f∶ X →(exp A B) ∧ g∶X → (exp A B) ∧
            (ev A B) o ⟨p1 A X,f o (p2 A X)⟩ =
            (ev A B) o ⟨p1 A X,g o (p2 A X)⟩ ⇒
            f = g
Proof
rw[] >>
‘f = tp ((ev A B) o ⟨p1 A X,f o (p2 A X)⟩)’
 by metis_tac[is_tp,ev_of_pair_hom] >>
‘g = tp ((ev A B) o ⟨p1 A X,g o (p2 A X)⟩)’
 by metis_tac[is_tp,ev_of_pair_hom] >>
metis_tac[]
QED

Theorem compose_with_p1:        
∀A B X f. f∶ X→ (A×B) ⇒ p1 A B ∘ f ∶ X → A
Proof
metis_tac[ax1_3,compose_hom]
QED

Theorem compose_with_p2:        
∀A B X f. f∶ X→ (A×B) ⇒ p2 A B ∘ f ∶ X → B
Proof
metis_tac[ax1_3,compose_hom]
QED        
        
Theorem to_p_eq:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
Proof
rw[EQ_IMP_THM] >>
metis_tac[compose_with_p1,compose_with_p2,ax1_3]
QED                   


Theorem to_p_eq_applied:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ∧
         (p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇒ f = g
Proof
metis_tac[to_p_eq]
QED

Theorem p1_hom[simp]:
∀A B. p1 A B∶ A×B → A
Proof
metis_tac[ax1_3]
QED


Theorem p2_hom[simp]:
∀A B. p2 A B∶ A×B → B
Proof
metis_tac[ax1_3]
QED                

Theorem p1_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p1 A B) o ⟨f,g⟩ = f
Proof
metis_tac[ax1_3]
QED

Theorem p2_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p2 A B) o ⟨f,g⟩ = g
Proof
metis_tac[ax1_3]
QED        


Theorem compose_assoc_SYM:
∀f g h A B C D. f∶A → B ∧ g∶B → C ∧ h∶C → D ⇒ h ∘ g ∘ f = (h ∘ g) ∘ f
Proof
metis_tac[compose_assoc]
QED
           
Theorem parallel_p_compose:
∀A B C D P Q f g i j. f∶ A → C ∧ g∶ B → D ∧ i∶ C → P ∧ j∶ D → Q ⇒
                      ⟨i o p1 C D,j o p2 C D⟩ o ⟨f o p1 A B, g o p2 A B⟩ =
                      ⟨i o f o p1 A B, j o g o p2 A B⟩
Proof
rw[] >> irule to_p_eq_applied >> qexistsl_tac [‘P’,‘Q’,‘A×B’] >>
‘⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩∶A×B → (P×Q)’
  by
   (‘i ∘ f ∘ p1 A B∶ (A×B) → P ∧ j ∘ g ∘ p2 A B∶ (A×B) → Q’
     suffices_by metis_tac[ax1_3] >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
(*??????*)
‘⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩∶A×B → (P×Q)’
  by
   (irule compose_hom >> qexists_tac ‘C×D’ >>
   metis_tac[compose_hom,ax1_3]) >>
‘⟨f ∘ p1 A B,g ∘ p2 A B⟩∶ (A×B) → (C × D)’ by metis_tac[compose_hom,ax1_3] >>
‘⟨i ∘ p1 C D,j ∘ p2 C D⟩∶ (C × D) → (P × Q)’ by metis_tac[compose_hom,ax1_3] >>
‘p1 P Q ∘ ⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩  = i ∘ f ∘ p1 A B’
  by (irule p1_of_pa >> qexists_tac ‘A×B’ >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ f ∘ p1 A B,j ∘ g ∘ p2 A B⟩ = j ∘ g ∘ p2 A B’
  by (irule p2_of_pa >> qexists_tac ‘A×B’ >>
     metis_tac[compose_hom,compose_assoc,ax1_3]) >>
fs[] >>
‘p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ = i ∘ p1 C D’
  by (irule p1_of_pa >> qexists_tac ‘C×D’ >>  metis_tac[compose_hom,ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ = j ∘ p2 C D’
   by (irule p2_of_pa >> qexists_tac ‘C×D’ >>  metis_tac[compose_hom,ax1_3]) >>
‘p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 (p1 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
 by (irule compose_assoc_SYM >> qexistsl_tac [‘A×B’,‘C×D’,‘P×Q’,‘P’] >>
    rw[] >> metis_tac[ax1_3]) >>
‘p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩ ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 (p2 P Q ∘ ⟨i ∘ p1 C D,j ∘ p2 C D⟩) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
 by (irule compose_assoc_SYM >> qexistsl_tac [‘A×B’,‘C×D’,‘P×Q’,‘Q’] >>
     rw[] >> metis_tac[ax1_3]) >>
‘(i ∘ p1 C D) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 i ∘ p1 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
  by metis_tac[compose_assoc,ax1_3] >>
‘(j ∘ p2 C D) ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ =
 j ∘ p2 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩’
  by metis_tac[compose_assoc,ax1_3] >>
fs[] >>
‘p1 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ = f ∘ p1 A B’
  by (irule p1_of_pa >> qexists_tac ‘A×B’ >> simp[] >>
     metis_tac[compose_hom,ax1_3]) >>
‘p2 C D ∘ ⟨f ∘ p1 A B,g ∘ p2 A B⟩ = g ∘ p2 A B’
  by (irule p2_of_pa >> qexists_tac ‘A×B’ >> simp[] >>
     metis_tac[compose_hom,ax1_3]) >>
fs[]
QED

Theorem parallel_p_one_side:
∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,g o f o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩
Proof
(* rw[] >> 
‘id A∶A → A ∧ f∶B → C ∧ id A∶ A → A ∧ g ∶ C → D ⇒
              ⟨(id A) ∘ p1 A C, g ∘ p2 A C⟩ ∘ ⟨id A ∘ p1 A B, f ∘ p2 A B⟩ =
              ⟨(id A) ∘ (id A) ∘ p1 A B,g ∘ f ∘ p2 A B⟩’
               by metis_tac[parallel_p_compose] >>
fs[] >>
‘p1 A B∶ A × B → A’ by metis_tac[p1_hom] >>
‘id A ∘ id A ∘ p1 A B = p1 A B’ by metis_tac[idL,compose_hom,compose_assoc] >>
fs[] >>
‘id A ∘ p1 A B = p1 A B ∧ id A o p1 A C = p1 A C’ by metis_tac[idL,p1_hom] >>
fs[] why line by line okay...*) cheat
QED

Theorem parallel_p_one_side':
∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,(g o f) o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩
Proof
rw[] >>
‘(g o f) o p2 A B = g o f o p2 A B’ suffices_by metis_tac[parallel_p_one_side]>>
metis_tac[p2_hom,compose_assoc]
QED                                  
                      
Theorem iterated_p_eq:
∀X A B C f g. f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ⇒
              (f = g ⇔
              (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
              (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
              (p2 (A×B) C) o f = (p2 (A×B) C) o g)
Proof
rw[EQ_IMP_THM] >> irule to_p_eq_applied >>
qexists_tac ‘A × B’ >> qexists_tac ‘C’ >> qexists_tac ‘X’ (*???*) >>
rw[] >>
‘p1 (A × B) C ∘ f ∶ X → (A × B) ∧  p1 (A × B) C ∘ g∶ X → (A × B)’
  by metis_tac[p1_hom,compose_hom] >>
irule to_p_eq_applied >>
qexistsl_tac [‘A’,‘B’,‘X’] >> rw[]
QED

Theorem iterated_p_eq_applied:
∀X A B C f g. (f∶X → ((A×B)×C) ∧ g∶X → ((A×B)×C) ∧ 
               (p1 A B) o (p1 (A×B) C) o f =  (p1 A B) o (p1 (A×B) C) o g ∧
               (p2 A B) o (p1 (A×B) C) o f =  (p2 A B) o (p1 (A×B) C) o g ∧
               (p2 (A×B) C) o f = (p2 (A×B) C) o g) ⇒ f = g
Proof
metis_tac[iterated_p_eq]
QED

(*        
Theorem iterated_projection:
*)

Theorem comm_with_s_id:
∀f. f∶ N → N ∧ f o z = z ∧ f o s = s o f ⇒ f = id N
Proof
cheat
QED

(*above theorem WRONG need correction*)        

Theorem to_p_eq_one_side:
∀A B f g. f∶ A → B ∧ g∶ A → B ∧ ⟨id A,f⟩ = ⟨id A,g⟩ ⇒ f = g
Proof
rw[] >> ‘p2 A B o ⟨id A,f⟩ = p2 A B o ⟨id A,g⟩’ by metis_tac[] >>
metis_tac[id1,p2_of_pa]
QED


(*for thm2*)

Definition is_subset_def:
is_subset a A ⇔ is_mono a ∧ cod a = A
End

Definition is_mem_def:
is_mem x a A ⇔ is_subset a A ∧ x∶ one → A ∧ ∃x0. x0∶ one → dom a ∧ a o x0 = x
End

Definition is_inc_def:
is_inc a b A ⇔ is_subset a A ∧ is_subset b A ∧ ∃h. h∶(dom a) → (dom b) ∧ b o h = a
End

Theorem is_mono_thm:
∀A B m. m∶ A → B ⇒
        (is_mono m ⇔
        (∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g))
Proof
rw[hom_def,is_mono_def] >> metis_tac[]
QED      


Theorem is_mono_applied:
∀A B m. m∶ A → B ∧
        (∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g) ⇒
        is_mono m
Proof
metis_tac[is_mono_thm]        
QED              

Theorem post_inv_mono:
∀A B m i. m∶ A → B ∧ i∶ B → A ∧ (i o m) = id A ⇒ is_mono m
Proof
rw[] >> irule is_mono_applied >> qexistsl_tac [‘A’,‘B’] >> rw[] >>
‘i o m o f = i o m o g’ by metis_tac[] >>
‘(i o m) o f = (i o m) o g’ by metis_tac[compose_assoc,compose_hom] >>
metis_tac[idL]
QED

Definition is_epi_def:
is_epi f ⇔ ∀g1 g2. dom g1 = dom g2 ∧ cod g1 = cod g2 ∧ dom g1 = cod f ∧ g1 o f = g2 o f ⇒ g1 = g2
End

Theorem is_epi_thm:
∀e A B. e∶ A → B ⇒
       (is_epi e ⇔ (∀X f g. f∶ B → X ∧ g∶ B → X ∧ f o e = g o e ⇒ f = g))
Proof
metis_tac[hom_def,is_epi_def]
QED


Theorem is_epi_applied:
∀e A B. e∶ A → B ∧ (∀X f g. f∶ B → X ∧ g∶ B → X ∧ f o e = g o e ⇒ f = g) ⇒
       is_epi e
Proof
metis_tac[is_epi_thm]
QED        
       
Theorem pre_inv_epi:
∀A B e i. e∶ A → B ∧ i∶ B → A ∧ e o i = id B ⇒ is_epi e
Proof
rw[] >> irule is_epi_applied >> qexistsl_tac [‘A’,‘B’] >> rw[] >>
‘(f o e) o i = (g o e) o i’ by metis_tac[] >>
‘f o e o i = g o e o i’ by metis_tac[compose_assoc,compose_hom] >>
metis_tac[idR]
QED

Theorem pb_exists:
∀X Y Z f g. f∶ X → Z ∧ g∶ Y → Z ⇒ ∃P b q. p∶ P → X ∧ q∶ P → Y ∧ f o f = q o g ∧
            (∀A u v. u∶ A → P ∧ v∶ A → Q ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
Proof
cheat
QED             
                
Theorem pb_mono_mono:

Proof                

Theorem cop eq iff component eq        

Proof

Theorem surj_is_epi:
∀A B f. f∶ A → B ∧ (∀b. one → B ⇒ ∃x0. x0∶ one → A ∧ f o x0 = x) ⇒ is_epi f
Proof
cheat
QED

                


        
Theorem is_iso_thm:
∀f A B. f∶ A → B ⇒
        (is_iso f ⇔
         ∃f'. f'∶ B → A ∧ f' o f = id A ∧ f o f' = id B)
Proof
metis_tac[is_iso_def,hom_def]
QED
        
Theorem are_iso_is_iso:
∀A B. A ≅ B ⇔ ∃f. f∶ A → B ∧ is_iso f
Proof
rw[are_iso_def] >> metis_tac[is_iso_thm]
QED
        
Theorem mono_epi_is_iso:
∀a. is_mono a ∧ is_epi a ⇒ is_iso a
Proof
cheat
QED

        
Theorem distinct_endo_exists:
∃X e1 e2. e1∶ X → X ∧ e2∶ X → X ∧ e1 ≠ e2
Proof
cheat
QED

Theorem fun_ext:
∀A B f g. f∶ A → B ∧ g∶ A → B ∧ (∀a. a∶ one → A ⇒ f o a = g o a) ⇒ f = g
Proof
metis_tac[ax4]
QED

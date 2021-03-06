open ETCSaxiomTheory;  
open HolKernel Parse boolLib bossLib;

val _ = new_theory "basic"



    
fun pairs_from_list l =
 case l of [] => []
          | (a :: l0) => (map (fn b => (b,a)) l0) @ (map (fn b => (a,b)) l0) @ (pairs_from_list l0)    

fun chom (thm1,thm2) = SOME (MATCH_MP compose_hom (CONJ thm1 thm2))
                       handle HOL_ERR _ => NONE
          
fun comptac (asl,t) =
 let val athms = map ASSUME asl 
     val ps = pairs_from_list athms
     val thms = List.mapPartial chom ps
 in
    map_every strip_assume_tac thms
 end (asl,t)

fun triples_from_list l =
 case l of [] => []
          | (a :: l0) =>  (map (fn b => (a, fst b, snd b)) (pairs_from_list l0)) @
                          (map (fn b => (fst b, a, snd b)) (pairs_from_list l0)) @
                          (map (fn b => (fst b, snd b, a)) (pairs_from_list l0)) @
                          (triples_from_list l0)


fun ahom (thm1,thm2,thm3) = SOME (MATCH_MP compose_assoc (CONJ thm1 (CONJ thm2 thm3)))
                            handle HOL_ERR _ => NONE  

fun assoctac (asl,t) =
 let val athms = map ASSUME asl
     val ts = triples_from_list athms
     val thms = List.mapPartial ahom ts
 in
    map_every strip_assume_tac thms
 end (asl,t)


    

Theorem compose_assoc_4_3_left:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  (f4 ∘ f3 ∘ f2) ∘ f1 = f4 ∘ f3 ∘ f2 ∘ f1
Proof
gs[hom_def,compose_assoc0,compose_hom0]
QED  




Theorem compose_assoc_4_2_left:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  (f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1
Proof
rw[] >>
‘f4 o f3∶ Z → B’ by metis_tac[compose_hom] >> 
‘(f4 ∘ f3) ∘ f2 ∘ f1 = ((f4 ∘ f3) ∘ f2) ∘ f1’
 by metis_tac[compose_assoc,compose_hom] >>
‘((f4 ∘ f3) ∘ f2)  = f4 o f3 o f2’ by metis_tac[compose_assoc] >>
rw[] >> 
metis_tac[compose_assoc_4_3_left]
QED


Theorem compose_assoc_4_2_middle:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  f4 o (f3 o f2) o f1 = f4 o f3 o f2 o f1
Proof
gs[hom_def,compose_assoc0,compose_hom0]
QED        


Theorem compose_assoc_4_2_middle_SYM:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  f4 o f3 o f2 o f1 = f4 o (f3 o f2) o f1
Proof
metis_tac[compose_assoc_4_2_middle]
QED        
           


Theorem compose_assoc_4_2_left_SYM:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  f4 o f3 o f2 o f1 = (f4 o f3) o f2 o f1
Proof
metis_tac[compose_assoc_4_2_left]
QED        



Theorem compose_assoc_4_3_2_left:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  (f4 o f3 o f2) o f1 = (f4 o f3) o f2 o f1
Proof
metis_tac[compose_assoc_4_3_left,compose_assoc_4_2_left]
QED
        


Theorem compose_assoc_4_2_left_middle:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  (f4 o f3) o f2 o f1 = f4 o (f3 o f2) o f1
Proof
rw[] >>
‘(f4 o f3) o f2 o f1 = f4 o f3 o f2 o f1’ by metis_tac[compose_assoc_4_2_left]>>
metis_tac[compose_assoc]
QED



Theorem compose_assoc_4_2_left_left:
∀A B X Y Z f1 f2 f3 f4.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ⇒
  ((f4 o f3) o f2) o f1 = f4 o f3 o f2 o f1
Proof
rw[] >>
‘f4 o f3∶ Z → B’ by metis_tac[compose_hom] >>
‘((f4 o f3) o f2) o f1 = (f4 o f3) o f2 o f1’ by metis_tac[compose_assoc]>>
metis_tac[compose_assoc_4_2_left]
QED                

Theorem o_bracket_left:
∀X Y Z A a b c d f g.
 f o b o a = g o d o c ∧ a∶ X → Y ∧ c∶ X → Y ∧ b∶ Y → Z ∧ d∶ Y → Z ∧
 f∶ Z → A ∧ g∶ Z → A ⇒ (f o b) o a = (g o d) o c
Proof
metis_tac[compose_assoc]
QED

        

Theorem o_bracket_right:
∀X Y Z A a b c d f g.
 (f o b) o a = (g o d) o c ∧ a∶ X → Y ∧ c∶ X → Y ∧ b∶ Y → Z ∧ d∶ Y → Z ∧
 f∶ Z → A ∧ g∶ Z → A ⇒ f o b o a = g o d o c
Proof
metis_tac[compose_assoc]
QED        

Theorem compose_assoc_5_2_left1_left:
∀A B C X Y Z f1 f2 f3 f4 f5.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C ⇒
  f5 o (f4 o f3) o f2 o f1 = (f5 o f4) o f3 o f2 o f1
Proof
rw[] >> rpt (CHANGED_TAC comptac) >>rpt (CHANGED_TAC assoctac) >> metis_tac[]
QED



Theorem compose_assoc_6_3_2_left_middle:
∀A B C D X Y Z f1 f2 f3 f4 f5 f6.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C /\ f6∶ C → D ⇒
  (f6 o f5 o f4) o f3 o f2 o f1 = f6 o f5 o (f4 o f3) o f2 o f1
Proof
gs[hom_def,compose_assoc0,compose_hom0]
QED



Theorem compose_assoc_6_left_left_left_right2:
∀A B C D X Y Z f1 f2 f3 f4 f5 f6.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C /\ f6∶ C → D ⇒
  (((f6 o f5 o f4) o f3) o f2) o f1 = f6 o f5 o f4 o (f3 o f2) o f1
Proof
gs[hom_def,compose_assoc0,compose_hom0]
QED
                


                              
(*
val _ = augment_srw_ss [SatisfySimps.SATISFY_ss]*)

(*    
fun pairs_from_list l =
 case l of [] => []
          | (a :: l0) => (map (fn b => (b,a)) l0) @ (map (fn b => (a,b)) l0) @ (pairs_from_list l0)    

fun chom (thm1,thm2) = SOME (MATCH_MP compose_hom (CONJ thm1 thm2))
                       handle HOL_ERR _ => NONE
          
fun comptac (asl,t) =
 let val athms = map ASSUME asl 
     val ps = pairs_from_list athms
     val thms = List.mapPartial chom ps
 in
    map_every strip_assume_tac thms
 end (asl,t)


fun triples_from_list l =
 case l of [] => []
          | (a :: l0) =>  (map (fn b => (a, fst b, snd b)) (pairs_from_list l0)) @
                          (map (fn b => (fst b, a, snd b)) (pairs_from_list l0)) @
                          (map (fn b => (fst b, snd b, a)) (pairs_from_list l0)) @
                          (triples_from_list l0)


fun ahom (thm1,thm2,thm3) = SOME (MATCH_MP compose_assoc (CONJ thm1 (CONJ thm2 thm3)))
                            handle HOL_ERR _ => NONE

fun assoctac (asl,t) =
 let val athms = map ASSUME asl
     val ts = triples_from_list athms
     val thms = List.mapPartial ahom ts
 in
    map_every strip_assume_tac thms
 end (asl,t)
              

                          
Definition triples_from_list:
triples_from_list [] = [] ∧
triples_from_list (a :: l) = (MAP (λb. (a, FST b, SND b)) (pairs_from_list l)) ++
                             (MAP (λb. (FST b, a, SND b)) (pairs_from_list l)) ++
                             (MAP (λb. (FST b, SND b, a)) (pairs_from_list l)) ++
                             (triples_from_list l)
End 


 
Definition pairs_from_list:
pairs_from_list [] = [] ∧
pairs_from_list (a :: l) = (MAP (λb. (b,a)) l) ++ (MAP (λb. (a,b)) l) ++ (pairs_from_list l)
End
*)

(*
chom (TRUTH,TRUTH)                      

List.mapPartial

val t = hd (#1 $ top_goal ())

strip_comb t

T ~~ F            *)
                
Theorem compose_assoc_5_4_left:
∀A B C X Y Z f1 f2 f3 f4 f5.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C ⇒
  f5 o f4 o f3 o f2 o f1 = (f5 o f4 o f3 o f2) o f1
Proof
rpt strip_tac >> rpt (CHANGED_TAC comptac) >>
rpt (CHANGED_TAC assoctac)  >> metis_tac[]
QED                 



Theorem compose_assoc_5_4_left_SYM:
∀A B C X Y Z f1 f2 f3 f4 f5.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C ⇒
  (f5 o f4 o f3 o f2) o f1 = f5 o f4 o f3 o f2 o f1
Proof
metis_tac[compose_assoc_5_4_left]
QED


Theorem compose_assoc_5_2_left:
∀A B C X Y Z f1 f2 f3 f4 f5.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C ⇒
  (f5 o f4) o f3 o f2 o f1 = f5 o f4 o f3 o f2 o f1
Proof
gs[hom_def,compose_assoc0,compose_hom0]
QED

Theorem compose_assoc_5_2_left_SYM:
∀A B C X Y Z f1 f2 f3 f4 f5.
  f1∶ X → Y ∧ f2∶ Y → Z ∧ f3∶ Z → A ∧ f4∶ A → B ∧ f5∶ B → C ⇒
  f5 o f4 o f3 o f2 o f1 = (f5 o f4) o f3 o f2 o f1
Proof
metis_tac[compose_assoc_5_2_left]
QED
                         

Theorem ax1_5_applied:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eq_induce f g h ∶X → eqo f g ∧
             eqa f g ∘ (eq_induce f g h) = h
Proof
metis_tac[ax1_5]             
QED


Theorem eq_induce_hom:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eq_induce f g h ∶X → eqo f g
Proof
metis_tac[ax1_5]             
QED




Theorem coeq_induce_hom:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶B → X ∧ h o f = h o g ⇒
             coeq_induce f g h ∶ coeqo f g → X
Proof
metis_tac[ax1_6]             
QED

         

Theorem eq_fac:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶X → A ∧ f ∘ h = g ∘ h ⇒
             eqa f g ∘ (eq_induce f g h) = h
Proof
metis_tac[ax1_5]             
QED



Theorem eq_fac_unique:
∀A B f g X h. f ∘ h = g ∘ h /\
              f∶A → B ∧ g∶A → B ∧ h∶X → A ⇒
              (!h0. (h0∶ X → eqo f g /\ eqa f g ∘ h0 = h) <=>
                   h0 = (eq_induce f g h))
Proof
metis_tac[ax1_5]             
QED        

(*above and below slow metis*)

Theorem coeq_fac:
∀A B f g X h. f∶A → B ∧ g∶A → B ∧ h∶B → X ∧ h o f = h o g ⇒
              (coeq_induce f g h)  o coeqa f g = h
Proof
metis_tac[ax1_6]             
QED



Theorem coeq_fac_unique:
∀A B f g X h. h o f = h o g /\
              f∶A → B ∧ g∶A → B ∧ h∶B → X ⇒
              (!h0. (h0∶  coeqo f g → X /\ h0 o coeqa f g = h) <=>
                   h0 = (coeq_induce f g h))
Proof
metis_tac[ax1_6]             
QED                 

Theorem to1_hom:
∀A. to1 A∶ A → one
Proof
metis_tac[ax1_1]
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

Theorem copa_hom:
∀A B X f g. f∶ A→ X ∧ g∶ B→ X ⇒ copa f g ∶ (A + B)→ X
Proof
metis_tac[ax1_4]
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

Theorem compose_with_i1:
∀A B X f. f∶ (A + B) → X ⇒ f o (i1 A B)∶ A → X
Proof
metis_tac[ax1_4,compose_hom]
QED         

Theorem compose_with_p2:        
∀A B X f. f∶ X→ (A×B) ⇒ p2 A B ∘ f ∶ X → B
Proof
metis_tac[ax1_3,compose_hom]
QED


Theorem compose_with_i2:
∀A B X f. f∶ (A + B) → X ⇒ f o (i2 A B)∶ B → X
Proof
metis_tac[ax1_4,compose_hom]
QED        
        
Theorem to_p_eq:
∀f g X A B. f∶ X → (A×B) ∧ g∶ X → (A × B) ⇒
            ((p1 A B) o f = (p1 A B) o g ∧ (p2 A B) o f = (p2 A B) o g ⇔ f = g)
Proof
rw[EQ_IMP_THM] >>
metis_tac[compose_with_p1,compose_with_p2,ax1_3]
QED

Theorem from_cop_eq:
∀f g X A B. f∶ (A+ B) → X ∧ g∶ (A + B) → X ⇒
            (f o (i1 A B) = g o (i1 A B) ∧ f o (i2 A B) = g o (i2 A B) ⇔ f = g)
Proof
rw[EQ_IMP_THM] >> metis_tac[compose_with_i1,compose_with_i2,ax1_4]
QED               

Theorem to1_unique:
∀A f g. f∶ A → one ∧ g∶ A → one ⇒ f = g
Proof
metis_tac[ax1_1]
QED


Theorem from0_unique:
∀B f g. f∶ zero → B ∧ g∶ zero → B ⇒ f = g
Proof
metis_tac[ax1_2]
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

Theorem i1_hom[simp]:
∀A B. i1 A B∶ A → A + B
Proof
metis_tac[ax1_4]
QED
        

Theorem p2_hom[simp]:
∀A B. p2 A B∶ A×B → B
Proof
metis_tac[ax1_3]
QED


Theorem i2_hom[simp]:
∀A B. i2 A B∶ B → A + B
Proof
metis_tac[ax1_4]
QED                 

Theorem p1_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p1 A B) o ⟨f,g⟩ = f
Proof
metis_tac[ax1_3]
QED

Theorem i1_of_copa:
∀A B X f g. f∶ A → X ∧ g∶ B → X ⇒ copa f g o i1 A B = f
Proof
metis_tac[ax1_4]
QED        

Theorem p2_of_pa:
∀A B X f g. f∶ X → A ∧ g∶ X → B ⇒ (p2 A B) o ⟨f,g⟩ = g
Proof
metis_tac[ax1_3]
QED

Theorem i2_of_copa:
∀A B X f g. f∶ A → X ∧ g∶ B → X ⇒ copa f g o i2 A B = g
Proof
metis_tac[ax1_4]
QED


Theorem i1_ne_i2:
i1 one one ≠ i2 one one
Proof
SPOSE_NOT_THEN ASSUME_TAC >>
‘∃X x1 x2. x1∶one → X ∧ x2∶one → X ∧ x1 ≠ x2’ by metis_tac[ax8] >>
‘copa x1 x2∶ one + one → X ∧ copa x1 x2 ∘ i1 one one = x1 ∧ copa x1 x2 ∘ i2 one one = x2’
  by metis_tac[ax1_4] >>
metis_tac[]
QED
  
       
Theorem prop_5_lemma:
∀A B x. ¬(x∶one → (A + B) ∧ (∃x0 x0'. x0∶one → A ∧ x0'∶one → B ∧
                             i1 A B ∘ x0 = x ∧
                             i2 A B ∘ x0' = x))
Proof
rpt strip_tac >> (* fs[is_mem_def] >>*)
‘i1 one one∶ one → (one + one) ∧ i2 one one ∶ one → (one + one)’
  by metis_tac[i1_hom,i2_hom] >>
‘to1 A∶ A → one ∧ to1 B∶ B → one’ by metis_tac[ax1_1] >>
‘(i1 one one) o to1 A∶ A → (one + one) ∧
 (i2 one one) o to1 B∶ B → (one + one)’ by metis_tac[compose_hom] >>
‘copa ((i1 one one) o to1 A) ((i2 one one) o to1 B)∶
 (A + B) → one + one’ by metis_tac[copa_hom] >>
‘copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o i1 A B o x0 =
 copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o i2 A B o x0'’
 by metis_tac[] >>
‘copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o i1 A B =
      (i1 one one) o to1 A’ by metis_tac[i1_of_copa] >>
‘copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o i2 A B =
      (i2 one one) o to1 B’ by metis_tac[i2_of_copa] >>
‘copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o
     i1 A B o x0 = i1 one one ∧
 copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o
     i2 A B o x0'= i2 one one’
  suffices_by metis_tac[i1_ne_i2] >>
‘i1 A B∶ A → (A + B)’ by metis_tac[i1_hom] >>
‘i2 A B∶ B → (A + B)’ by metis_tac[i2_hom] >>
‘dom (i1 A B) = A ∧ dom (i2 A B) = B’ by metis_tac[hom_def] >>
‘copa (i1 one one ∘ to1 A) (i2 one one ∘ to1 B) ∘ i1 A B ∘ x0 =
 (copa (i1 one one ∘ to1 A) (i2 one one ∘ to1 B) ∘ i1 A B) ∘ x0 ∧
 copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o i2 A B o x0'=
 (copa ((i1 one one) o to1 A) ((i2 one one) o to1 B) o
     i2 A B) o x0'’
 by metis_tac[compose_assoc] >>
simp[] >>
‘(i1 one one ∘ to1 A) ∘ x0  = i1 one one ∘ to1 A ∘ x0 ∧
 (i2 one one ∘ to1 B) ∘ x0' = i2 one one ∘ to1 B ∘ x0'’
 by metis_tac[compose_assoc] >>
‘to1 A ∘ x0 = id one ∧ to1 B ∘ x0' = id one’
 suffices_by metis_tac[idR] >>
‘to1 A ∘ x0∶ one → one ∧ to1 B ∘ x0'∶ one → one’
 by metis_tac[compose_hom] >>
metis_tac[to1_unique,id1]
QED 


Theorem prop_5:
∀A B x. ¬(is_mem x (i1 A B) (A + B) ∧ is_mem x (i2 A B) (A + B))
Proof
rpt strip_tac >>  fs[is_mem_def] >> metis_tac[prop_5_lemma,hom_def,i1_hom,i2_hom]
QED
 
               

Theorem i1_i2_disjoint:
!X t. t∶ one → X ==> i1 X X o t <> i2 X X o t
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘(∃x. x∶one → (X + X) ∧ (∃x0 x0'. x0∶one → X ∧ x0'∶one → X ∧
                             i1 X X ∘ x0 = x ∧
                             i2 X X ∘ x0' = x))’
  suffices_by metis_tac[prop_5_lemma] >>
qexists_tac ‘i1 X X o t’ >> metis_tac[i1_hom,compose_hom]
QED

        
Theorem po_with_one:
∀A. po A one ≅ A
Proof
rw[are_iso_def] >> qexistsl_tac [‘p1 A one’,‘⟨id A,to1 A⟩’]>>
‘p1 A one∶A × one → A’ by metis_tac[p1_hom] >>
‘to1 A∶ A → one’ by metis_tac[to1_hom] >> 
‘⟨id A,to1 A⟩∶A → (A × one)’ by metis_tac[id1,pa_hom] >>
‘p1 A one ∘ ⟨id A,to1 A⟩ = id A’ by metis_tac[p1_of_pa,id1] >>
rw[] >> irule to_p_eq_applied >>
qexistsl_tac [‘A’,‘one’,‘A×one’] >> simp[] >>
‘⟨id A,to1 A⟩ ∘ p1 A one∶A × one → (A × one)’ by metis_tac[compose_hom]>>
‘p1 A one ∘ id (A × one) = p1 A one ∧ p2 A one ∘ id (A × one) = p2 A one’
  by metis_tac[idR,id1,p2_hom] >>
‘p1 A one ∘ ⟨id A,to1 A⟩ ∘ p1 A one =
 (p1 A one ∘ ⟨id A,to1 A⟩) ∘ p1 A one’ by metis_tac[compose_assoc] >>
‘p2 A one ∘ ⟨id A,to1 A⟩ ∘ p1 A one =
 (p2 A one ∘ ⟨id A,to1 A⟩) ∘ p1 A one’ by metis_tac[compose_assoc,p2_hom]>>
‘(p2 A one ∘ ⟨id A,to1 A⟩) = to1 A’ by metis_tac[id1,p2_of_pa] >>
rw[] (* 2 *)
>- metis_tac[idL]
>- (irule to1_unique >> qexists_tac ‘A×one’ >>
   ‘p2 A one∶A × one → one’ by metis_tac[p2_hom] >>
   metis_tac[compose_hom])
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
rw[] >>
‘(id A)∶A → A ∧ f∶B → C ∧ id A∶ A → A ∧ g∶ C → D ⇒
   ⟨(id A) ∘ p1 A C, g ∘ p2 A C⟩ ∘ ⟨id A ∘ p1 A B, f ∘ p2 A B⟩ =
   ⟨(id A) ∘ (id A) ∘ p1 A B,g ∘ f ∘ p2 A B⟩’
  by metis_tac[parallel_p_compose] >>
fs[] >>
‘p1 A B∶ A × B → A’ by metis_tac[p1_hom] >>
‘id A ∘ id A ∘ p1 A B = p1 A B’ by metis_tac[idL,compose_hom,compose_assoc] >>
fs[] >>
‘id A ∘ p1 A B = p1 A B ∧ id A o p1 A C = p1 A C’ by metis_tac[idL,p1_hom] >>
fs[]
QED

Theorem parallel_p_one_side':
∀A B C D f g.f∶ B → C ∧ g∶ C→ D ⇒
             ⟨p1 A B,(g o f) o p2 A B⟩ =
             ⟨p1 A C, g o p2 A C⟩ o ⟨p1 A B, f o p2 A B⟩
Proof
rw[] >>
‘(g o f) o p2 A B = g o f o p2 A B’ suffices_by metis_tac[parallel_p_one_side]>> metis_tac[p2_hom,compose_assoc]
QED

Theorem parallel_p_one_side_three:
∀A B C D E f g h.
         f∶B → C ∧ g∶C → D /\ h ∶ D → E ⇒
         ⟨p1 A B,(h o g ∘ f) ∘ p2 A B⟩ =
         ⟨p1 A D, h ∘ p2 A D⟩ o ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩
Proof
rw[] >> irule to_p_eq_applied >>
‘⟨p1 A B,(h ∘ g ∘ f) ∘ p2 A B⟩∶ (A×B) → (A × E)’ by metis_tac[pa_hom,compose_hom,p1_hom,p2_hom] >>
‘⟨p1 A D,h ∘ p2 A D⟩∶ (A×D) →(A × E)’ by metis_tac[p1_hom,p2_hom,compose_hom,pa_hom] >>
‘⟨p1 A C,g ∘ p2 A C⟩∶ (A×C) →(A × D)’ by metis_tac[p1_hom,p2_hom,compose_hom,pa_hom] >>
‘⟨p1 A B,f ∘ p2 A B⟩∶ (A×B) →(A × C)’ by metis_tac[p1_hom,p2_hom,compose_hom,pa_hom] >>
‘⟨p1 A D,h ∘ p2 A D⟩ ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩∶ (A×B) → (A × E)’
 by metis_tac[compose_hom] >>
qexistsl_tac [‘A’,‘E’,‘(A×B)’] >> simp[] >>
‘(h ∘ g ∘ f) ∘ p2 A B ∶ (A×B) → E’ by metis_tac[p2_hom,compose_hom] >>
‘p1 A E ∶ (A× E) → A’ by metis_tac[p1_hom] >>
‘p2 A E ∶ (A× E) → E’ by metis_tac[p2_hom] >>
‘p1 A D ∶ (A× D) → A’ by metis_tac[p1_hom] >>
‘p2 A D ∶ (A× D) → D’ by metis_tac[p2_hom] >>
‘p1 A C ∶ (A× C) → A’ by metis_tac[p1_hom] >>
‘p2 A C ∶ (A× C) → C’ by metis_tac[p2_hom] >> rw[]
>- (‘p1 A E ∘ ⟨p1 A B,(h ∘ g ∘ f) ∘ p2 A B⟩ = p1 A B’
     by metis_tac[p1_of_pa,p1_hom] >>
   ‘p1 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩ ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
    (p1 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩) ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
    by
     (‘(p1 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩) ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘
        ⟨p1 A B,f ∘ p2 A B⟩ =
      p1 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩ ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘
        ⟨p1 A B,f ∘ p2 A B⟩’ suffices_by metis_tac[] >>
     irule compose_assoc_4_2_left >> metis_tac[]) >>
   simp[] >>
   ‘(p1 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩) = p1 A D’ by metis_tac[p1_hom,p2_hom,compose_hom,p1_of_pa] >>
   simp[] >>
   ‘p1 A D ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
    (p1 A D ∘ ⟨p1 A C,g ∘ p2 A C⟩) ∘ ⟨p1 A B,f ∘ p2 A B⟩’
    by metis_tac[compose_assoc] >>
   simp[] >>
   ‘p1 A D ∘ ⟨p1 A C,g ∘ p2 A C⟩ = p1 A C’ by metis_tac[p1_hom,p2_hom,compose_hom,p1_of_pa] >>
   simp[] >> metis_tac[p1_hom,p2_hom,compose_hom,p1_of_pa])
>- (‘p2 A E ∘ ⟨p1 A B,(h ∘ g ∘ f) ∘ p2 A B⟩ = (h ∘ g ∘ f) ∘ p2 A B’
     by metis_tac[p1_hom,p2_of_pa] >>
   simp[] >>
   ‘p2 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩ ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
    (p2 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩) ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩’
    by metis_tac[compose_assoc_4_2_left] >>
   ‘p2 A E ∘ ⟨p1 A D,h ∘ p2 A D⟩ = h ∘ p2 A D’
    by metis_tac[compose_hom,p2_of_pa,p2_hom] >>
   simp[] >>
   ‘(h ∘ p2 A D) ∘ ⟨p1 A C,g ∘ p2 A C⟩ ∘ ⟨p1 A B,f ∘ p2 A B⟩ =
    h ∘ (p2 A D ∘ ⟨p1 A C,g ∘ p2 A C⟩) ∘ ⟨p1 A B,f ∘ p2 A B⟩’
     by metis_tac[compose_assoc_4_2_left_middle] >>
   ‘(p2 A D ∘ ⟨p1 A C,g ∘ p2 A C⟩) = g ∘ p2 A C’ by (irule p2_of_pa >> metis_tac[compose_hom]) >>
   simp[] >>
   ‘h ∘ (g ∘ p2 A C) ∘ ⟨p1 A B,f ∘ p2 A B⟩ = h ∘ g ∘ p2 A C ∘ ⟨p1 A B,f ∘ p2 A B⟩’
    by metis_tac[compose_assoc_4_2_left_middle,compose_assoc_4_2_left] >>
   simp[] >>
   ‘p2 A C ∘ ⟨p1 A B,f ∘ p2 A B⟩ = f ∘ p2 A B’
    by (irule p2_of_pa >> metis_tac[compose_hom,p1_hom,p2_hom]) >>
   simp[] >> metis_tac[compose_assoc_4_3_left,p2_hom])
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

        
Theorem N_ind_z_s_id:
id N = N_ind z s
Proof
‘∀x. x∶N → N ∧ x ∘ z = z ∧ x ∘ s = s ∘ x ⇔ x = N_ind z s’
by metis_tac[ax3] >>
metis_tac[idL,idR,id1,ax3]
QED

Theorem comm_with_s_id:
∀f. f∶ N → N ∧ f o z = z ∧ f o s = s o f ⇒ f = id N
Proof
rw[] >>
‘∀x. x∶N → N ∧ x ∘ z = z ∧ x ∘ s = s ∘ x ⇔ x = N_ind z s’
  by metis_tac[ax3] >>
‘id N = N_ind z s’ suffices_by metis_tac[] >>
metis_tac[N_ind_z_s_id]
QED
    

Theorem to_p_eq_one_side:
∀A B f g. f∶ A → B ∧ g∶ A → B ∧ ⟨id A,f⟩ = ⟨id A,g⟩ ⇒ f = g
Proof
rw[] >> ‘p2 A B o ⟨id A,f⟩ = p2 A B o ⟨id A,g⟩’ by metis_tac[] >>
metis_tac[id1,p2_of_pa]
QED


(*for thm2*)


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

Theorem is_mono_property:
∀A B m. is_mono m ∧ m∶ A → B ⇒
(∀X f g. f∶ X → A ∧ g∶ X → A ∧ m o f = m o g ⇒ f = g)
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

Theorem is_epi_property:
∀e A B. is_epi e ∧ e∶ A → B ⇒
        (∀X f g. f∶ B → X ∧ g∶ B → X ∧ f o e = g o e ⇒ f = g)
Proof
metis_tac[is_epi_thm]
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

Definition is_pb_def:
is_pb P p q f g <=> cod f = cod g /\ p∶ P → dom f ∧ q∶ P → dom g /\
                      f o p = g o q ∧
                      (∀A u v. u∶ A → dom f ∧ v∶ A → dom g ∧ f o u = g o v ⇒
                      ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
End


Theorem eqa_hom:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ eqa f g∶eqo f g → A
Proof
metis_tac[ax1_5]
QED


Theorem coeqa_hom:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ coeqa f g ∶B → (coeqo f g)
Proof
metis_tac[ax1_6]
QED
        
Theorem eq_equlity:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ f ∘ eqa f g = g ∘ eqa f g
Proof
metis_tac[ax1_5]
QED

Theorem coeq_equlity:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ coeqa f g  o f = coeqa f g o g
Proof
metis_tac[ax1_6]
QED


Theorem coeq_of_equal:
!f A B. f∶ A → B ==> ?ki. ki∶ coeqo f f → B /\ ki o (coeqa f f) = id B
Proof
rw[] >> qexists_tac ‘coeq_induce f f (id B)’  >> rw[] >>
metis_tac[coeq_induce_hom,id1,coeq_fac]
QED 

Theorem eqa_is_mono:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_mono (eqa f g)
Proof
rw[] >> irule is_mono_applied >> qexistsl_tac [‘eqo f g’,‘A’] >>
‘eqa f g∶eqo f g → A’ by metis_tac[eqa_hom] >>
rw[] >>
‘f o eqa f g ∘ f' = (f o eqa f g) ∘ f'’ by metis_tac[compose_assoc] >>
‘f ∘ eqa f g = g ∘ eqa f g’ by metis_tac[eq_equlity] >>
‘(f o eqa f g) ∘ f' = (g o eqa f g) ∘ f'’ by metis_tac[] >>
‘(g o eqa f g) ∘ f' = g o eqa f g ∘ f'’ by metis_tac[compose_assoc] >>
‘f o eqa f g ∘ f' = g o eqa f g ∘ f'’ by metis_tac[] >>
‘eqa f g o f'∶ X → A’ by metis_tac[compose_hom] >>
‘∀x0. x0∶X → eqo f g ∧ eqa f g ∘ x0 = eqa f g o f' ⇔
      x0 = eq_induce f g (eqa f g o f')’ by metis_tac[ax1_5] >>
metis_tac[]
QED

Theorem coeqa_is_epi:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_epi (coeqa f g)
Proof
rw[] >> irule is_epi_applied >> qexistsl_tac [‘B’,‘coeqo f g’] >>
‘coeqa f g∶B → coeqo f g’ by metis_tac[coeqa_hom] >> rw[] >>
‘coeqa f g ∘ f = coeqa f g ∘ g’ by metis_tac[coeq_equlity] >>
‘f' o coeqa f g ∘ f = f' o coeqa f g ∘ g’ by metis_tac[] >>
‘(f' o coeqa f g) ∘ f = (f' o coeqa f g) ∘ g’ by metis_tac[o_bracket_left] >>
‘(f' ∘ coeqa f g)∶ B → X’ by metis_tac[compose_hom] >>
‘∀x0. x0∶coeqo f g → X ∧ x0 ∘ coeqa f g = (f' ∘ coeqa f g) ⇔
      x0 = coeq_induce f g (f' ∘ coeqa f g)’ by metis_tac[ax1_6] >>
metis_tac[]      
QED
        

Theorem pb_exists:
∀X Y Z f g. f∶ X → Z ∧ g∶ Y → Z ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃!a. a∶ A → P ∧ p o a = u ∧ q o a = v)
Proof
rw[] >>
qexistsl_tac [‘eqo (f o p1 X Y) (g o p2 X Y)’,
              ‘p1 X Y o (eqa (f o p1 X Y) (g o p2 X Y))’,
              ‘p2 X Y o (eqa (f o p1 X Y) (g o p2 X Y))’] >>
‘p1 X Y∶(X×Y)→ X ∧ p2 X Y∶ (X × Y) → Y’ by metis_tac[p1_hom,p2_hom] >>
‘(f o p1 X Y)∶ (X×Y) → Z ∧  (g o p2 X Y)∶ (X×Y) → Z’ by metis_tac[compose_hom]>>
‘(eqa (f o p1 X Y) (g o p2 X Y))∶ eqo (f o p1 X Y) (g o p2 X Y) → (X × Y)’
  by metis_tac[eqa_hom] >>
‘p1 X Y o (eqa (f o p1 X Y) (g o p2 X Y))∶ eqo (f o p1 X Y) (g o p2 X Y) → X’
  by metis_tac[compose_hom] >>
‘(p2 X Y) o (eqa (f o p1 X Y) (g o p2 X Y))∶ eqo (f o p1 X Y) (g o p2 X Y) → Y’
  by (irule compose_hom >> qexists_tac ‘X × Y’ >> rw[]) >> 
qabbrev_tac ‘E = eqo (f o p1 X Y) (g o p2 X Y)’ >>
qabbrev_tac ‘e =  (eqa (f o p1 X Y) (g o p2 X Y))’ >>
qabbrev_tac ‘e1 = p1 X Y o e’ >>
qabbrev_tac ‘e2 = p2 X Y o e’ >>
‘f ∘ e1 = g ∘ e2’
 by (simp[Abbr‘e1’,Abbr‘e2’] >>
    ‘(f ∘ p1 X Y) ∘ e = (g ∘ p2 X Y) ∘ e’
     suffices_by metis_tac[compose_assoc] >>
    simp[Abbr‘e’] >> metis_tac[eq_equlity]) >>
simp[] >> rw[] >>
‘⟨u,v⟩∶ A → (X × Y)’ by metis_tac[pa_hom] >>
‘(f o p1 X Y) o ⟨u,v⟩ = (g o p2 X Y) o ⟨u,v⟩’
  by
   (‘f o p1 X Y o ⟨u,v⟩ = g o p2 X Y o ⟨u,v⟩’
     suffices_by metis_tac[compose_assoc] >>
    ‘p1 X Y o ⟨u,v⟩ = u ∧ p2 X Y o ⟨u,v⟩ = v’
     by metis_tac[p1_of_pa,p2_of_pa] >>
    simp[]) >>
drule eq_fac_unique >> rw[] >>
first_x_assum (qspecl_then [‘X×Y’,‘Z’,‘A’] assume_tac) >>
‘∀h0. (h0∶A → E ∧ e ∘ h0 = ⟨u,v⟩ ⇔
       h0 = eq_induce (f ∘ p1 X Y) (g ∘ p2 X Y) ⟨u,v⟩)’
  by metis_tac[] >> 
rw[EXISTS_UNIQUE_THM] (* 2 *) 
>- (qexists_tac ‘eq_induce (f ∘ p1 X Y) (g ∘ p2 X Y) ⟨u,v⟩’ >>
   ‘eq_induce (f ∘ p1 X Y) (g ∘ p2 X Y) ⟨u,v⟩∶A → E’
     by
      (simp[Abbr‘E’] >> metis_tac[eq_induce_hom]) >>
   simp[Abbr‘e1’,Abbr‘e2’] >> 
   ‘p1 X Y ∘ e ∘ eq_induce (f ∘ p1 X Y) (g ∘ p2 X Y) ⟨u,v⟩ = u ∧
    p2 X Y ∘ e ∘ eq_induce (f ∘ p1 X Y) (g ∘ p2 X Y) ⟨u,v⟩ = v’
    suffices_by metis_tac[compose_assoc] >>
   ‘p1 X Y ∘ ⟨u,v⟩ = u ∧
    p2 X Y ∘ ⟨u,v⟩ = v’ suffices_by metis_tac[] >>
   metis_tac[p1_of_pa,p2_of_pa])
>- (‘e o a = e o a'’
     suffices_by
      (‘is_mono e’ by (simp[Abbr‘e’] >> metis_tac[eqa_is_mono]) >>
       metis_tac[is_mono_property]) >>
   ‘e o a∶ A → (X × Y) ∧ e o a'∶ A → (X× Y)’
    by metis_tac[compose_hom] >>
   irule to_p_eq_applied >> qexistsl_tac [‘X’,‘Y’,‘A’] >>
   simp[] >>
   ‘e1 ∘ a = e1 ∘ a' ∧ e2 ∘ a = e2 ∘ a' ⇒
    p1 X Y ∘ e ∘ a = p1 X Y ∘ e ∘ a' ∧ p2 X Y ∘ e ∘ a = p2 X Y ∘ e ∘ a'’
   suffices_by metis_tac[] >>
   simp[Abbr‘e1’,Abbr‘e2’] >>
   metis_tac[compose_assoc])
QED

(*
        
Theorem pb_exists_thm = SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM] pb_exists        


val pb_def = new_specification ("pb_def",["pbo","pb1","pb2"],pb_exists_thm)*)
        (*
Theorem test:
!A. ?B. A = B
Proof
simp[]
QED

Theorem test' = SIMP_RULE bool_ss [SKOLEM_THM] test        

val test_def = new_specification ("test_def",["test"],test')       
*)

Theorem pb_fac_exists:
∀X Y Z f g. g∶ Y → Z ∧  f∶ X → Z  ⇒ ∃P p q. p∶ P → X ∧ q∶ P → Y ∧ f o p = g o q ∧
            (∀A u v. u∶ A → X ∧ v∶ A → Y ∧ f o u = g o v ⇒
             ∃a. a∶ A → P ∧ p o a = u ∧ q o a = v)
Proof
rw[] >> drule pb_exists >> strip_tac >>
first_x_assum (qspecl_then [‘Y’,‘g’] assume_tac) >>
fs[EXISTS_UNIQUE_ALT] >> metis_tac[]
QED

Theorem pb_mono_mono:
!P p q f g. is_pb P p q f g /\ is_mono g ==> is_mono p
Proof
rw[] >> irule is_mono_applied >> fs[is_pb_def] >>
qabbrev_tac ‘X = dom f’ >>
qabbrev_tac ‘Y = dom g’ >>
qexistsl_tac [‘P’,‘X’] >> simp[] >> rw[] >>
rename [‘p ∘ k1 = p ∘ k2’] >>
‘f o p o k1 = f o p o k2’ by metis_tac[] >>
qabbrev_tac ‘Z = cod f’ >>
‘f∶ X → Z ∧ g∶ Y → Z’ by metis_tac[hom_def,Abbr‘X’,Abbr‘Y’] >>
‘f o p o k1 = (f o p) o k1’ by metis_tac[compose_assoc] >>
‘f ∘ p ∘ k2 = (f ∘ p) ∘ k2’ by metis_tac[compose_assoc] >>
‘(g ∘ q) o k1 = (g ∘ q) o k2’ by metis_tac[] >>
‘g ∘ q o k1 = g ∘ q o k2’ by metis_tac[compose_assoc] >>
‘q o k1∶ X' → Y ∧ q o k2∶ X' → Y’ by metis_tac[compose_hom] >> 
‘q o k1 = q o k2’ by metis_tac[is_mono_property] >>
first_x_assum (qspecl_then [‘X'’,‘p o k1’,‘q o k1’] assume_tac) >>
‘p ∘ k1∶X' → X ∧ q ∘ k1∶X' → Y’ by metis_tac[compose_hom] >>
‘f ∘ p ∘ k1 = g ∘ q ∘ k1’ by metis_tac[compose_assoc] >>
‘∃a. ∀a'. a'∶X' → P ∧ p ∘ a' = p ∘ k1 ∧ q ∘ a' = q ∘ k1 ⇔ a = a'’
 by metis_tac[] >>
metis_tac[]
QED                

(*behaviour of metis weird in above thm*)
(*
Theorem eqa_hom:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ eqa f g∶eqo f g → A
Proof
metis_tac[ax1_5]
QED


Theorem coeqa_hom:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ coeqa f g ∶B → (coeqo f g)
Proof
metis_tac[ax1_6]
QED
        
Theorem eq_equlity:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ f ∘ eqa f g = g ∘ eqa f g
Proof
metis_tac[ax1_5]
QED

Theorem coeq_equlity:
∀A B f g.
         f∶A → B ∧ g∶A → B ⇒ coeqa f g  o f = coeqa f g o g
Proof
metis_tac[ax1_6]
QED


Theorem coeq_of_equal:
!f A B. f∶ A → B ==> ?ki. ki∶ coeqo f f → B /\ ki o (coeqa f f) = id B
Proof
rw[] >> qexists_tac ‘coeq_induce f f (id B)’  >> rw[] >>
metis_tac[coeq_induce_hom,id1,coeq_fac]
QED 

Theorem eqa_is_mono:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_mono (eqa f g)
Proof
rw[] >> irule is_mono_applied >> qexistsl_tac [‘eqo f g’,‘A’] >>
‘eqa f g∶eqo f g → A’ by metis_tac[eqa_hom] >>
rw[] >>
‘f o eqa f g ∘ f' = (f o eqa f g) ∘ f'’ by metis_tac[compose_assoc] >>
‘f ∘ eqa f g = g ∘ eqa f g’ by metis_tac[eq_equlity] >>
‘(f o eqa f g) ∘ f' = (g o eqa f g) ∘ f'’ by metis_tac[] >>
‘(g o eqa f g) ∘ f' = g o eqa f g ∘ f'’ by metis_tac[compose_assoc] >>
‘f o eqa f g ∘ f' = g o eqa f g ∘ f'’ by metis_tac[] >>
‘eqa f g o f'∶ X → A’ by metis_tac[compose_hom] >>
‘∀x0. x0∶X → eqo f g ∧ eqa f g ∘ x0 = eqa f g o f' ⇔
      x0 = eq_induce f g (eqa f g o f')’ by metis_tac[ax1_5] >>
metis_tac[]
QED

Theorem coeqa_is_epi:
∀A B f g. f∶ A → B ∧ g∶ A → B ⇒ is_epi (coeqa f g)
Proof
rw[] >> irule is_epi_applied >> qexistsl_tac [‘B’,‘coeqo f g’] >>
‘coeqa f g∶B → coeqo f g’ by metis_tac[coeqa_hom] >> rw[] >>
‘coeqa f g ∘ f = coeqa f g ∘ g’ by metis_tac[coeq_equlity] >>
‘f' o coeqa f g ∘ f = f' o coeqa f g ∘ g’ by metis_tac[] >>
‘(f' o coeqa f g) ∘ f = (f' o coeqa f g) ∘ g’ by metis_tac[o_bracket_left] >>
‘(f' ∘ coeqa f g)∶ B → X’ by metis_tac[compose_hom] >>
‘∀x0. x0∶coeqo f g → X ∧ x0 ∘ coeqa f g = (f' ∘ coeqa f g) ⇔
      x0 = coeq_induce f g (f' ∘ coeqa f g)’ by metis_tac[ax1_6] >>
metis_tac[]      
QED

*)        
        
Theorem non_zero_pinv:
∀A B f. f∶ A → B ∧ ¬(A ≅ zero) ⇒ ∃g. g∶B → A ∧ f ∘ g ∘ f = f
Proof
metis_tac[ax5,ax6]
QED

Theorem epi_pinv_pre_inv:
∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_epi f ∧ f ∘ g ∘ f = f ⇒ f o g = id B
Proof
rw[] >> drule is_epi_property >> rw[] >>
first_x_assum (qspecl_then [‘A’,‘B’,‘B’,‘f o g’,‘id B’] assume_tac) >>
first_x_assum irule >> metis_tac[compose_hom,compose_assoc,idL,id1]
QED

Theorem mono_pinv_post_inv:
∀A B f g. f∶ A → B ∧ g∶B → A ∧ is_mono f ∧ f ∘ g ∘ f = f ⇒
          g o f = id A
Proof
rw[] >> drule is_mono_property >> rw[] >>
first_x_assum (qspecl_then [‘A’,‘B’,‘A’,‘id A’,‘g o f’] assume_tac)>>
‘id A = g o f’ suffices_by metis_tac[] >>
first_x_assum irule >> metis_tac[id1,idR,compose_hom]
QED
        

Theorem epi_non_zero_pre_inv:
∀A B f. f∶ A → B ∧ is_epi f ∧ ¬(A ≅ zero) ⇒ ∃g. g∶ B → A ∧ f o g = id B
Proof
metis_tac[non_zero_pinv,epi_pinv_pre_inv]
QED


        
Theorem mono_non_zero_post_inv:
∀A B f. f∶ A → B ∧ is_mono f ∧ ¬(A ≅ zero) ⇒ ∃g. g∶ B → A ∧ g o f = id A
Proof
metis_tac[non_zero_pinv,mono_pinv_post_inv]
QED       

Theorem o_mono_mono:
∀A B C f g. is_mono f ∧ is_mono g ∧ f∶ A → B ∧ g∶ B → C ⇒ is_mono (g o f)
Proof
rw[] >> irule is_mono_applied >> qexistsl_tac [‘A’,‘C’] >>
‘g o f∶ A → C’ by metis_tac[compose_hom] >>
rw[] >> drule is_mono_property >> rw[] >>
‘g ∘ f ∘ f' = g ∘ f ∘ g'’ by metis_tac[compose_assoc] >>
‘f o g' ∶ X → B’ by metis_tac[compose_hom] >>
‘f o f' ∶ X → B’ by metis_tac[compose_hom] >>
‘f o f' = f o g'’ by metis_tac[] >>
Q.UNDISCH_THEN `is_mono g` (K ALL_TAC) >>
drule is_mono_property >>
strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem is_iso_thm:
∀f A B. f∶ A → B ⇒
        (is_iso f ⇔
         ∃f'. f'∶ B → A ∧ f' o f = id A ∧ f o f' = id B)
Proof
metis_tac[is_iso_def,hom_def]
QED        

Theorem mono_o_iso_mono:
!A B X f i. is_iso i /\ is_mono f /\ f∶ A → B /\ i∶ X → A ==> (is_mono (f o i))
Proof
rw[] >> irule is_mono_applied >> drule is_mono_property >> rw[] >>
qexistsl_tac [‘X’,‘B’] >> rw[] >-
(‘i o f'∶ X' → A ∧ i o g∶ X' → A’ by metis_tac[compose_hom] >>
‘f ∘ i ∘ f' = f ∘ i ∘ g’ by metis_tac[compose_assoc] >>
‘i o f' = i o g’ by metis_tac[] >>
‘∃i'. i'∶ A → X ∧ i' o i = id X’ by metis_tac[is_iso_thm] >>
‘i' o i ∘ f' = i' o i ∘ g’ by metis_tac[] >>
metis_tac[id1,compose_assoc,idL]) >>
metis_tac[compose_hom]
QED 
 
Theorem o_mono_imp_mono:
∀A B C f m. f∶ A → B ∧ m∶ B → C ∧ is_mono (m o f) ⇒ is_mono f
Proof        
rw[] >> irule is_mono_applied >> qexistsl_tac [‘A’,‘B’] >> rw[] >>
‘m o f o f' = m o f o g’ by metis_tac[] >>
drule is_mono_property >>
‘m o f∶ A → C’ by metis_tac[compose_hom] >>
metis_tac[compose_assoc]
QED


Theorem o_epi_imp_epi:
∀A B C f e. f∶ A → B ∧ e∶ C → A ∧ is_epi (f o e) ⇒ is_epi f
Proof
rw[] >> irule is_epi_applied >> qexistsl_tac [‘A’,‘B’] >> rw[] >>
‘f' o f o e = g o f o e’ by metis_tac[compose_assoc] >>
drule is_epi_property >>
‘f o e∶ C → B’ by metis_tac[compose_hom] >>
metis_tac[compose_assoc]
QED
        

Theorem fun_ext:
∀A B f g. f∶ A → B ∧ g∶ A → B ∧ (∀a. a∶ one → A ⇒ f o a = g o a) ⇒ f = g
Proof
metis_tac[ax4]
QED
        
Theorem surj_is_epi:
∀A B f. f∶ A → B ∧ (∀b. b∶ one → B ⇒ ∃b0. b0∶ one → A ∧ f o b0 = b) ⇒ is_epi f
Proof
rw[] >> irule is_epi_applied >> qexistsl_tac [‘A’,‘B’] >> rw[] >>
rename [‘t1 o f = t2 o f’] >>
irule fun_ext >> qexistsl_tac [‘B’,‘X’] >> rw[] >>
first_x_assum drule >> rw[] >> metis_tac[compose_assoc]
QED
        
Theorem are_iso_is_iso:
∀A B. A ≅ B ⇔ ∃f. f∶ A → B ∧ is_iso f
Proof
rw[are_iso_def] >> metis_tac[is_iso_thm]
QED

Theorem are_iso_is_iso':
∀A B. A ≅ B ⇔ ∃f. f∶ B → A ∧ is_iso f
Proof
rw[are_iso_def] >> metis_tac[is_iso_thm]
QED
        

Theorem o_iso_eq_eq:
∀A B X f g i. is_iso i ∧ f∶ A→ B ∧ g∶ A → B ∧ i∶ X → A ∧ f o i = g o i ⇒ f = g
Proof
rw[] >> ‘∃i'. i'∶ A → X ∧ i o i' = id A’ by metis_tac[is_iso_thm] >>
‘f o i o i' = g o i o i'’ by metis_tac[compose_assoc] >>
metis_tac[idR]
QED  

Theorem from_iso_zero_eq:
∀A B f g. A≅ zero ∧ f∶ A → B ∧ g∶ A → B ⇒ f = g
Proof
rw[] >> ‘∃i. i∶ zero → A ∧ is_iso i’ by metis_tac[are_iso_is_iso'] >>
‘f o i∶ zero → B ∧ g o i∶ zero → B’ by metis_tac[compose_hom] >>
‘f o i = g o i’ by metis_tac[from0_unique] >>
metis_tac[o_iso_eq_eq]
QED

   
Theorem eq_pre_o_eq:
∀X Y Z a b c d f A. b o a = d o c ∧ a∶ X → Y ∧ b∶ Y → Z ∧ c∶ X → Y ∧ d∶ Y → Z ∧
                  f∶ A → X ⇒ b o a o f = d o c o f
Proof
metis_tac[compose_assoc]
QED

Theorem one_to_one_id:
∀f. f∶ one → one ⇒ f = id one
Proof
rw[]  >> metis_tac[id1,to1_unique]
QED
        
           
Theorem no_epi_from_zero:
∀f A B. is_epi f ∧ f∶ A → B ∧ ¬(B≅ zero) ⇒ ¬(A ≅ zero)
Proof
rw[] >> drule is_epi_property >>rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘to1 B∶ B → one’ by metis_tac[to1_hom] >>
‘i1 one one∶ one → (one + one) ∧ i2 one one∶ one → (one + one)’ by metis_tac[ax1_4] >>
drule from_iso_zero_eq >>
strip_tac >>
first_x_assum (qspecl_then [‘one + one’,‘(i1 one one) o (to1 B) o f’,
                            ‘(i2 one one) o (to1 B) o f’] assume_tac) >>
‘i1 one one ∘ to1 B ∘ f∶A → one + one ∧
 i2 one one ∘ to1 B ∘ f∶A → one + one ’  by metis_tac[compose_hom] >>
first_x_assum drule_all >> strip_tac >>
‘i1 one one ∘ to1 B ∘ f = (i1 one one ∘ to1 B) ∘ f ∧
 i2 one one ∘ to1 B ∘ f = (i2 one one ∘ to1 B) ∘ f’
 by metis_tac[compose_assoc] >>
‘(i1 one one ∘ to1 B) = (i2 one one ∘ to1 B)’
  suffices_by
   (strip_tac >>
    ‘∃b. b∶ one → B’ by metis_tac[ax6] >>
    ‘i1 one one ∘ to1 B o b = i2 one one ∘ to1 B o b’
      by metis_tac[eq_pre_o_eq] >>
    ‘to1 B ∘ b∶ one → one’ by metis_tac[compose_hom] >>
    ‘to1 B o b = id one’ by metis_tac[one_to_one_id] >>
    metis_tac[idR,i1_ne_i2]) >>
first_x_assum irule >>
rw[] (*2  *)
>- metis_tac[]
>- (qexistsl_tac [‘A’,‘B’,‘one + one’] >> simp[] >> metis_tac[compose_hom])
QED


Theorem epi_pre_inv:
∀A B f. is_epi f /\ f∶ A → B /\ ¬(B ≅ zero)⇒ ∃g. g∶ B → A ∧ f o g = id B
Proof
metis_tac[epi_non_zero_pre_inv,no_epi_from_zero]
QED        

Theorem zero_no_mem:
∀f. ¬(f∶ one → zero)
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘∀X f g. f∶ one → X ∧ g∶ one → X ⇒ f = g’ suffices_by metis_tac[ax8] >>
rw[] >>
‘f o to1 zero = id zero’
  by (irule from0_unique >> qexists_tac ‘zero’ >>
     metis_tac[ax1_1,compose_hom,id1]) >>
‘to1 zero o f = id one’
  by (irule to1_unique >> qexists_tac ‘one’ >>
     metis_tac[ax1_1,compose_hom,id1]) >>
‘is_iso (to1 zero)’ by metis_tac[is_iso_thm,ax1_1] >>
‘f' o (to1 zero) = g o (to1 zero)’
 by (irule from0_unique >> qexists_tac‘X’ >>
    ‘to1 zero∶ zero → one’ by metis_tac[ax1_1] >>
     metis_tac[compose_hom]) >>
‘to1 zero∶ zero → one’ by metis_tac[ax1_1] >>     
metis_tac[o_iso_eq_eq]
QED                


Theorem iso_zero_no_mem:
∀A. A≅ zero ⇒ ¬(∃x. x∶ one → A)
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘∃f. f∶ A → zero’ by metis_tac[are_iso_is_iso,is_iso_thm] >>
‘f o x∶ one→ zero’ by metis_tac[compose_hom] >>
metis_tac[zero_no_mem]
QED

Theorem is_epi_surj:
∀A B f. is_epi f /\ f∶ A → B ==> (∀b. b∶ one → B ⇒ ∃b0. b0∶ one → A ∧ f o b0 = b)
Proof
rw[] >> Cases_on ‘B≅ zero’ (* 2 *)
>- metis_tac[iso_zero_no_mem] >>
‘¬(A≅ zero)’ by metis_tac[no_epi_from_zero] >>
‘∃g. g∶B → A ∧ f ∘ g = id B’ by metis_tac[epi_non_zero_pre_inv] >>
qexists_tac ‘g o b’ >> metis_tac[compose_hom,compose_assoc,idL]
QED
   

Theorem distinct_endo_2:
copa (i1 one one) (i2 one one) ∶ (one + one) → (one + one) ∧
copa (i2 one one) (i1 one one) ∶ (one + one) → (one + one) ∧
copa (i1 one one) (i2 one one) ≠ copa (i2 one one) (i1 one one)
Proof
‘copa (i1 one one) (i2 one one) ∶ (one + one) → (one + one) ∧
copa (i2 one one) (i1 one one) ∶ (one + one) → (one + one)’ by metis_tac[ax1_4] >>
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘copa (i1 one one) (i2 one one) o (i1 one one)= (i1 one one) ∧
 copa (i2 one one) (i1 one one) o (i1 one one) = (i2 one one)’ by metis_tac[ax1_4] >>
metis_tac[from_cop_eq,i1_ne_i2]
QED


        
Theorem distinct_endo_exists:
∃X e1 e2. e1∶ X → X ∧ e2∶ X → X ∧ e1 ≠ e2
Proof
metis_tac[distinct_endo_2]        
QED




        (*
Theorem zero_no_mem:
∀f. ¬(f∶ one → zero)
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘∀X f g. f∶ one → X ∧ g∶ one → X ⇒ f = g’ suffices_by metis_tac[ax8] >>
rw[] >>
‘f o to1 zero = id zero’
  by (irule from0_unique >> qexists_tac ‘zero’ >>
     metis_tac[ax1_1,compose_hom,id1]) >>
‘to1 zero o f = id one’
  by (irule to1_unique >> qexists_tac ‘one’ >>
     metis_tac[ax1_1,compose_hom,id1]) >>
‘is_iso (to1 zero)’ by metis_tac[is_iso_thm,ax1_1] >>
‘f' o (to1 zero) = g o (to1 zero)’
 by (irule from0_unique >> qexists_tac‘X’ >>
    ‘to1 zero∶ zero → one’ by metis_tac[ax1_1] >>
     metis_tac[compose_hom]) >>
‘to1 zero∶ zero → one’ by metis_tac[ax1_1] >>     
metis_tac[o_iso_eq_eq]
QED        
*)

Theorem not_to_zero:
∀f A. f∶ A → zero ⇒ A ≅ zero
Proof
SPOSE_NOT_THEN ASSUME_TAC >> fs[] >> drule ax6 >> strip_tac >>
metis_tac[zero_no_mem,compose_hom]
QED             

Theorem to_zero_zero:
∀f A B. f∶ A → B /\ B ≅ zero ==> A ≅ zero
Proof
rw[] >> ‘∃i. i∶ B→ zero’ by metis_tac[are_iso_is_iso,is_iso_thm] >>
‘i o f∶ A → zero’ by metis_tac[compose_hom] >>
metis_tac[not_to_zero]
QED


Theorem to_iso_zero_iso:
!X A f. X ≅ zero /\  f∶ A → X ==> is_iso f
Proof
rw[] >>
‘A ≅ zero’ by metis_tac[to_zero_zero] >>
‘∃az za. az∶ A→ zero ∧ za∶ zero → A ∧ az o za = id zero ∧ za o az = id A’
 by metis_tac[are_iso_is_iso,is_iso_thm] >>
‘∃xz zx. xz∶ X→ zero ∧ zx∶ zero → X ∧ xz o zx = id zero ∧ zx o xz = id X’
 by metis_tac[are_iso_is_iso,is_iso_thm] >>
‘∃f'. f'∶ X → A ∧ f o f' = id X ∧ f' o f = id A’
 suffices_by metis_tac[is_iso_thm] >>
qexists_tac ‘za o xz’ >>
‘za ∘ xz∶X → A’ by metis_tac[compose_hom] >>
rw[] (* 2 *)
>- (irule from_iso_zero_eq >> qexistsl_tac [‘X’,‘X’] >> metis_tac[compose_hom,id1])
>- (irule from_iso_zero_eq >> qexistsl_tac [‘A’,‘A’] >> metis_tac[compose_hom,id1])
QED         


            
Theorem mono_epi_is_iso:
∀a. is_mono a ∧ is_epi a ⇒ is_iso a
Proof
rw[] >> qabbrev_tac ‘A = dom a’ >> qabbrev_tac ‘B = cod a’ >>
‘a∶ A → B’ by metis_tac[hom_def,Abbr‘A’,Abbr‘B’] >>
Cases_on ‘B≅ zero’ (* 2 *)
>- metis_tac[to_iso_zero_iso]
>- (‘¬(A≅ zero)’ by metis_tac[no_epi_from_zero,Abbr‘A’] >>
‘∃a'. a'∶ B → A ∧ a' o a = id A ∧ a o a' = id B’ suffices_by metis_tac[is_iso_thm] >>
‘∃g. g∶B → A ∧ a ∘ g ∘ a = a’ by metis_tac[ax5,ax6] >>
qexists_tac ‘g’ >> rw[] >> metis_tac[epi_pinv_pre_inv,mono_pinv_post_inv])
QED

Theorem to_copa_fac:
∀x A B.
         x∶one → A + B ⇒
         ∃x0. x0∶ one → A ∧ (i1 A B) o x0 = x ∨
         ∃x0. x0∶ one → B ∧ (i2 A B) o x0 = x
Proof
rw[] >> drule ax7 >> rw[is_mem_def] >>
metis_tac[hom_def,i1_hom,i2_hom]
QED

Theorem one_ne_zero:
¬(one ≅ zero)
Proof
SPOSE_NOT_THEN ASSUME_TAC >>
drule iso_zero_no_mem >> rw[] >> metis_tac[id1]
QED

        
Theorem tp_element_ev:
∀X Y f x. f∶ X→ Y ∧ x∶ one→ X ⇒
          ev X Y o ⟨x, tp (f o p1 X one)⟩ = f o x
Proof
rw[] >>
‘p1 X one∶ X × one → X ∧ p2 X one∶ (X × one) → one’ by metis_tac[p1_hom,p2_hom] >>
‘f o p1 X one∶ (X × one) → Y’ by metis_tac[compose_hom] >>
‘tp (f o p1 X one)∶ one → exp X Y’ by metis_tac[tp_hom] >> 
‘⟨x,tp (f ∘ p1 X one)⟩∶one → (X × exp X Y)’ by metis_tac[pa_hom] >>
‘⟨x,id one⟩ ∶one → (X × one)’ by metis_tac[id1,pa_hom] >>
‘⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩∶ (X × one) → (X × exp X Y)’
 by metis_tac[compose_hom,tp_hom,p1_hom,p2_hom,pa_hom] >>
‘⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ ∘ ⟨x,id one⟩∶one → (X × exp X Y)’
 by metis_tac[compose_hom] >>
‘p1 X (exp X Y)∶ (X × exp X Y) → X ∧
 p2 X (exp X Y)∶ (X × exp X Y) → exp X Y’ by metis_tac[p1_hom,p2_hom] >>
‘tp (f ∘ p1 X one) ∘ p2 X one∶ (X × one) → exp X Y’ by metis_tac[compose_hom] >>
‘⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩∶ (X × one) → (X × (exp X Y))’
 by metis_tac[pa_hom] >> 
‘⟨x, tp (f o p1 X one)⟩ = ⟨p1 X one,tp (f ∘ p1 X one) o p2 X one⟩ o  ⟨x,id one⟩’
 by (irule to_p_eq_applied >> qexistsl_tac [‘X’,‘exp X Y’,‘one’] >>
    simp[] >>
    ‘p1 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ ∘ ⟨x,id one⟩ =
     (p1 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩) ∘ ⟨x,id one⟩’
     by metis_tac[compose_assoc] >>
    ‘p2 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ ∘ ⟨x,id one⟩ =
     (p2 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩) ∘ ⟨x,id one⟩’
     by metis_tac[compose_assoc] >>
    simp[] >>
    ‘p1 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ = p1 X one’
     by metis_tac[p1_of_pa] >>
    ‘p2 X (exp X Y) ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ =
     tp (f ∘ p1 X one) ∘ p2 X one’ by metis_tac[p2_of_pa] >>
    ‘p1 X (exp X Y) ∘ ⟨x,tp (f ∘ p1 X one)⟩ = x’ by metis_tac[p1_of_pa] >>
    ‘p2 X (exp X Y) ∘ ⟨x,tp (f ∘ p1 X one)⟩ = tp (f o p1 X one)’ by metis_tac[p2_of_pa]>>
    simp[] >>
    ‘p1 X one ∘ ⟨x,id one⟩ = x’ by metis_tac[p1_of_pa,id1] >>
    ‘(tp (f ∘ p1 X one) ∘ p2 X one) ∘ ⟨x,id one⟩ =
     tp (f ∘ p1 X one) ∘ p2 X one ∘ ⟨x,id one⟩’ by metis_tac[compose_assoc] >>
    simp[] >>
    ‘p2 X one ∘ ⟨x,id one⟩ = id one’ by metis_tac[p2_of_pa,id1] >>
    simp[] >> metis_tac[idR]) >>
simp[] >>
‘ev X Y ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩ ∘ ⟨x,id one⟩ =
 (ev X Y ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩) ∘ ⟨x,id one⟩’
 by metis_tac[compose_assoc,ev_hom] >>
‘(ev X Y ∘ ⟨p1 X one,tp (f ∘ p1 X one) ∘ p2 X one⟩) = f o p1 X one’
 by metis_tac[ev_of_tp] >>
simp[] >> metis_tac[compose_assoc,id1,p1_of_pa]
QED

        
Theorem copa_not_mem_mono_mono:
is_mono a ∧ a∶ A → X ∧ x∶ one → X ∧
 ¬(∃x0. x0∶ one → A ∧ a o x0 = x) ⇒ is_mono (copa a x)
Proof
rw[] >> irule is_mono_applied >>
‘copa a x∶ (A + one) → X’ by metis_tac[copa_hom] >>
qexistsl_tac [‘A + one’,‘X’] >> rw[] >>
irule fun_ext >> qexistsl_tac [‘X'’,‘(A + one)’] >> rw[] >>
rename [‘x'∶ one → X'’] >>
‘f ∘ x'∶ one → A + one ∧ g o x'∶ one → A + one’
 by metis_tac[compose_hom] >>
‘∃f0. f0∶ one → A ∧ (i1 A one) o f0 = f o x' ∨
 ∃f0. f0∶ one → one ∧ (i2 A one) o f0 = f o x'’
 by metis_tac[to_copa_fac] (* 2 *)
>- (‘∃g0. g0∶ one → A ∧ (i1 A one) o g0 = g o x' ∨
    ∃g0. g0∶ one → one ∧ (i2 A one) o g0 = g o x'’
     by metis_tac[to_copa_fac] (* 2 *)
    >- (‘copa a x ∘ f o x' = copa a x ∘ g o x'’
        by metis_tac[compose_assoc] >>
       ‘copa a x ∘ i1 A one ∘ f0 = copa a x ∘ i1 A one ∘ g0’
        by metis_tac[] >>
       ‘(copa a x ∘ i1 A one) ∘ f0 = (copa a x ∘ i1 A one) ∘ g0’
        by metis_tac[compose_assoc,i1_hom] >>
       ‘a ∘ f0 = a ∘ g0’ by metis_tac[i1_of_copa] >>
       ‘f0 = g0’ by metis_tac[is_mono_property] >>
       metis_tac[])
    >- (‘a o f0 = x’ suffices_by metis_tac[] >>
       ‘copa a x ∘ f o x' = copa a x ∘ g o x'’
        by metis_tac[compose_assoc] >>
       ‘copa a x o i1 A one ∘ f0 = copa a x o i2 A one ∘ g0'’
        by metis_tac[] >>
       ‘copa a x o i1 A one ∘ f0 = (copa a x o i1 A one) ∘ f0’
        by metis_tac[compose_assoc,i1_hom] >>
       ‘copa a x o i2 A one ∘ g0' = (copa a x o i2 A one) ∘ g0'’
        by metis_tac[compose_assoc,i2_hom] >>
       ‘a o f0 = x o g0'’ by metis_tac[i1_of_copa,i2_of_copa] >>
       ‘g0' = id one’ by metis_tac[id1,to1_unique] >>
       metis_tac[idR]))
>- (‘∃g0. g0∶ one → A ∧ (i1 A one) o g0 = g o x' ∨
    ∃g0. g0∶ one → one ∧ (i2 A one) o g0 = g o x'’
     by metis_tac[to_copa_fac] (* 2 *)
    >- (‘a o g0 = x’ suffices_by metis_tac[] >>
       ‘copa a x ∘ f o x' = copa a x ∘ g o x'’
        by metis_tac[compose_assoc] >>
       ‘copa a x o i2 A one ∘ f0' = copa a x o i1 A one ∘ g0’
        by metis_tac[] >>
       ‘copa a x o i2 A one ∘ f0' = (copa a x o i2 A one) ∘ f0'’
        by metis_tac[compose_assoc,i2_hom] >>
       ‘copa a x o i1 A one ∘ g0 = (copa a x o i1 A one) ∘ g0’
        by metis_tac[compose_assoc,i1_hom] >>
       ‘x o f0' = a o g0’ by metis_tac[i1_of_copa,i2_of_copa] >> 
       ‘f0' = id one’ by metis_tac[id1,to1_unique] >>
       metis_tac[idR])
    >- (‘f0' = g0'’ by metis_tac[to1_unique] >>
        metis_tac[]))
QED

        

Theorem iso_symm:
∀X Y. X ≅ Y ⇔ Y ≅ X
Proof
rw[] >> simp[are_iso_is_iso] >> metis_tac[is_iso_thm]
QED    

Theorem iso_compose_iso:
∀X Y Z f g. is_iso f ∧ is_iso g ∧ f∶ X → Y ∧ g∶ Y → Z ⇒
            is_iso (g o f)
Proof
rw[] >>
‘∃f'. f'∶ Y → X ∧ f' o f = id X ∧ f o f' = id Y’
 by metis_tac[is_iso_thm] >>
‘∃g'. g'∶ Z → Y ∧ g' o g = id Y ∧ g o g' = id Z’
 by metis_tac[is_iso_thm] >>
‘g o f∶ X → Z’ by metis_tac[compose_hom] >>
drule is_iso_thm >> rw[] >>
qexists_tac ‘f' o g'’ >>
‘f' o g'∶ Z → X’ by metis_tac[compose_hom] >> simp[] >>
‘(f' ∘ g') ∘ g ∘ f = f' ∘ (g' ∘ g) ∘ f’
 by metis_tac[compose_assoc_4_2_left_middle] >>
‘(g ∘ f) ∘ f' ∘ g' = g ∘ (f ∘ f') ∘ g'’
 by metis_tac[compose_assoc_4_2_left_middle] >>
simp[] >> metis_tac[idL,idR]
QED    
       
Theorem iso_trans:
∀X Y Z. X ≅ Y ∧ Y ≅ Z ⇒ X ≅ Z
Proof
rw[are_iso_is_iso] >> qexists_tac ‘f' o f’ >> metis_tac[compose_hom,iso_compose_iso]
QED

Theorem iso_to_same:
∀X Y A. X ≅ A ∧ Y ≅ A ⇒ X ≅ Y
Proof
metis_tac[iso_symm,iso_trans]
QED        


    
Theorem inc_inc_iso0:
∀A X Y a b h1 h2. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
                  h1∶ X → Y ∧ h2∶ Y → X ∧
                  b o h1 = a ∧ a o h2 = b ⇒ X ≅ Y
Proof
rw[] >> Cases_on ‘X ≅ zero’ >> Cases_on ‘Y ≅ zero’
>- metis_tac[iso_to_same]
>- metis_tac[to_zero_zero]
>- metis_tac[to_zero_zero]
>- (qabbrev_tac ‘b = a o h2’ >>
   ‘∃b'. b'∶ A → Y ∧ b' o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   ‘∃a'. a'∶ A → X ∧ a' o a = id X’
    by metis_tac[mono_non_zero_post_inv] >>
   simp[are_iso_is_iso] >>
   qexists_tac ‘h1’ >>
   ‘h1 o h2 = id Y ∧ h2 o h1 = id X’
    suffices_by metis_tac[is_iso_thm] >>
   strip_tac (* 2 *)
   >- (‘b' o (a o h2) = id Y’
       by metis_tac[Abbr‘b’] >>
      ‘b' o b o h1 = b' o a’
       by metis_tac[] >>
      ‘h1 = b' o a’ by metis_tac[idL, compose_assoc] >>
      metis_tac[compose_assoc])
   >- (‘a' o a o h2 = a' o b’
       by metis_tac[Abbr‘b’] >>
      ‘h2 = a' o b’ by metis_tac[idL,compose_assoc] >>
      metis_tac[compose_assoc]))
QED


Theorem inc_inc_iso_as_subobj:
∀A X Y a b h1 h2. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
                  h1∶ X → Y ∧ h2∶ Y → X ∧
                  b o h1 = a ∧ a o h2 = b ⇒
         h1 o h2 = id Y ∧ h2 o h1 = id X
Proof
rw[] >> Cases_on ‘X ≅ zero’ >> Cases_on ‘Y ≅ zero’ (* 6 *)
>- metis_tac[from_iso_zero_eq,compose_hom,id1]
>- metis_tac[to_zero_zero]
>- metis_tac[to_zero_zero]
>- (qabbrev_tac ‘b = a o h2’ >>
   ‘∃b'. b'∶ A → Y ∧ b' o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   ‘∃a'. a'∶ A → X ∧ a' o a = id X’
    by metis_tac[mono_non_zero_post_inv] >>
   simp[are_iso_is_iso] >>
   ‘b' o (a o h2) = id Y’
       by metis_tac[Abbr‘b’] >>
      ‘b' o b o h1 = b' o a’
       by metis_tac[] >>
      ‘h1 = b' o a’ by metis_tac[idL, compose_assoc] >>
      metis_tac[compose_assoc])
>- metis_tac[from_iso_zero_eq,compose_hom,id1]
>- metis_tac[to_zero_zero]
>- metis_tac[to_zero_zero]
>- (qabbrev_tac ‘b = a o h2’ >>
   ‘∃b'. b'∶ A → Y ∧ b' o b = id Y’
    by metis_tac[mono_non_zero_post_inv] >>
   ‘∃a'. a'∶ A → X ∧ a' o a = id X’
    by metis_tac[mono_non_zero_post_inv] >>
   simp[are_iso_is_iso] >>
   ‘a' o a o h2 = a' o b’
       by metis_tac[Abbr‘b’] >>
   ‘h2 = a' o b’ by metis_tac[idL,compose_assoc] >>
   metis_tac[compose_assoc])
QED        

Theorem prop_2_half2:
∀X Y A a b. is_mono a ∧ is_mono b ∧ a∶ X → A ∧ b∶ Y → A ∧
            (∀x xb. x∶ one → A ∧ xb∶ one → X ∧ a o xb = x ⇒
                    ∃xb'. xb'∶ one → Y ∧ b o xb' = x) ⇒
            (∃h. h∶ X → Y ∧ b o h = a)
Proof
rpt strip_tac >> Cases_on ‘Y≅ zero’
>- (‘X ≅ zero’
     by
      (SPOSE_NOT_THEN ASSUME_TAC >>
      ‘∃x. x∶ one → X’ by metis_tac[ax6] >>
      ‘a o x∶ one → A’ by metis_tac[compose_hom] >>
      ‘∃xb'. xb'∶one → Y’ by metis_tac[] >>
      metis_tac[iso_zero_no_mem]) >>
   fs[are_iso_is_iso] >>
   ‘∃f''. f''∶zero → Y ∧ f'' ∘ f = id Y ∧ f ∘ f'' = id zero’
    by metis_tac[is_iso_thm] >>
   qexists_tac ‘f'' o f'’ >>
   ‘f'' ∘ f'∶X → Y’ by metis_tac[compose_hom] >> simp[] >>
   irule from_iso_zero_eq >> qexistsl_tac [‘X’,‘A’] >>
   metis_tac[compose_hom,are_iso_is_iso])    
>- (‘∃g. g∶ A → Y ∧ g o b = id Y’ 
    by metis_tac[mono_non_zero_post_inv] >>
   qexists_tac ‘g o a’ >> strip_tac
   >- metis_tac[compose_hom] >> 
   irule fun_ext >>
   ‘b ∘ g ∘ a∶ X → A ∧ a∶ X → A’ by metis_tac[compose_hom] >>
   qexistsl_tac [‘X’,‘A’] >> simp[] >> rpt strip_tac >>
   rename [‘x0∶ one → X’] >>
   first_x_assum (qspecl_then [‘a o x0’,‘x0’] assume_tac) >>
   ‘a o x0∶ one → A’ by metis_tac[compose_hom] >>
   fs[] >> rfs[] >>
   ‘(b ∘ g ∘ a) ∘ x0 = b ∘ g ∘ (a ∘ x0)’
    by metis_tac[compose_assoc_4_3_left] >>
   ‘b ∘ g ∘ a ∘ x0 = b o g o b o xb'’
    by metis_tac[] >>
   ‘b ∘ g ∘ b ∘ xb' = b ∘ (g ∘ b) ∘ xb'’
    by metis_tac[compose_assoc_4_2_left_middle,
                 compose_assoc_4_2_left] >>
   ‘b ∘ (g ∘ b) ∘ xb' = b o xb'’
     by metis_tac[idL] >>
   metis_tac[])
QED


Theorem prop_2_corollary:
∀X Y A a b. a∶ X → A ∧ b∶ Y → A ∧ is_mono a ∧ is_mono b ∧
            (∀y. y∶ one → Y ⇒ ∃x. x∶ one → X ∧ a o x = b o y) ∧
            (∀x. x∶ one → X ⇒ ∃y. y∶ one → Y ∧ a o x = b o y) ⇒
            X ≅ Y
Proof
rw[] >> irule inc_inc_iso0 >>
‘∃h1. h1∶ X → Y ∧ b o h1 = a’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
‘∃h2. h2∶ Y → X ∧ a o h2 = b’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
metis_tac[]
QED


Theorem prop_2_corollary_as_subobj:
∀X Y A a b. a∶ X → A ∧ b∶ Y → A ∧ is_mono a ∧ is_mono b ∧
            (∀y. y∶ one → Y ⇒ ∃x. x∶ one → X ∧ a o x = b o y) ∧
            (∀x. x∶ one → X ⇒ ∃y. y∶ one → Y ∧ a o x = b o y) ⇒
           ?h1 h2. b o h1 = a /\ a o h2 = b /\ h1∶X → Y ∧ h2∶Y → X ∧ h1 ∘ h2 = id Y ∧ h2 ∘ h1 = id X
Proof
rw[] >>
‘∃h1. h1∶ X → Y ∧ b o h1 = a’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
‘∃h2. h2∶ Y → X ∧ a o h2 = b’
 by (irule prop_2_half2 >> rw[] >> metis_tac[]) >>
qexistsl_tac [‘h1’,‘h2’] >> metis_tac[inc_inc_iso_as_subobj]
QED        

        


Definition is_refl_def:
is_refl f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃d. d∶ cod f1 → dom f1 ∧
                 f0 o d = id (cod f1) ∧
                 f1 o d = id (cod f1)
End


Definition is_symm_def:
is_symm f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
             ∃t. t∶ dom f1 → dom f1 ∧
                 f0 o t = f1 ∧
                 f1 o t = f0
End


Definition is_trans_def:
is_trans f0 f1 ⇔ dom f0 = dom f1 ∧ cod f0 = cod f1 ∧
                 ∀X h0 h1.
                  h0∶ X → dom f1 ∧ h1∶ X → dom f1 ∧
                  f1 o h0 = f0 o h1 ⇒
                  ∃u. u∶ X → dom f1 ∧
                      f0 o u = f0 o h0 ∧ f1 o u = f1 o h1
End

Theorem iso_zero_zero:
∀A. A≅ zero ⇒
   ∀X. ∃!f. f∶ A → X
Proof
rw[EXISTS_UNIQUE_ALT] >>
‘∃i. i∶A → zero ∧ is_iso i’ by metis_tac[are_iso_is_iso] >>
qexists_tac ‘(from0 X) o i’ >>
rw[EQ_IMP_THM] >> metis_tac[from_iso_zero_eq,ax1_2,compose_hom]
QED

Theorem epi_has_section:
∀e A B. is_epi e ∧ e∶ A → B ⇒ ∃s. s∶ B → A ∧ e o s = id B
Proof
rw[] >> Cases_on ‘B ≅ zero’
>- (drule iso_zero_zero >> rw[] >>
   fs[EXISTS_UNIQUE_ALT] >>
   ‘∃f. ∀f'. f'∶B → A ⇔ f = f'’ by metis_tac[] >>
   qexists_tac ‘f’ >>
   metis_tac[id1,compose_hom])
>- metis_tac[epi_pre_inv]
QED

        


Theorem fac_through_eq:
∀f g h h0 A B X. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ∧ h0∶ X → eqo f g ∧
           eqa f g o h0 = h ⇒
           f o h = g o h
Proof
rw[] >>
‘eqa f g∶ eqo f g → A’ by metis_tac[eqa_hom] >>
‘f ∘ eqa f g ∘ h0 = (f ∘ eqa f g) ∘ h0 ∧
 g ∘ eqa f g ∘ h0 = (g ∘ eqa f g) ∘ h0’
  by metis_tac[compose_assoc] >>
‘f ∘ eqa f g = g ∘ eqa f g’
 suffices_by metis_tac[compose_assoc] >>
metis_tac[eq_equlity]
QED

Theorem fac_through_eq_iff:
∀f g h. f∶ A → B ∧ g∶ A → B ∧ h∶ X → A ⇒
        ((∃h0. h0∶ X → eqo f g ∧ (eqa f g) o h0 = h) ⇔
         f o h = g o h)
Proof
rw[EQ_IMP_THM] (* 2 *)
>- metis_tac[fac_through_eq]
>- (qexists_tac ‘eq_induce f g h’ >> metis_tac[eq_induce_hom,eq_fac])
QED

val _ = export_theory();

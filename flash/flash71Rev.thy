theory flash71Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_InvVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv71:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak1VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak2VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak3VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX1VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX2VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX3VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX4VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX5VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX6VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX7VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8VsInv71:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8_homeVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX9VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10VsInv71:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10_homeVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX11VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_GetVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak1VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak2VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak3VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put1VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put2VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put3VsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutVsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutXAcksDoneVsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_ClearVsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Nak_HomeVsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_NakVsInv71:  
  (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_GetX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iRule2))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_GetX_Nak_HomeVsInv71:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_PutXVsInv71:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_PutX_HomeVsInv71:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak1VsInv71:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak2VsInv71:  
  (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3 , simp)

        apply(rule_tac x=" (neg ( andForm ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iRule1) )  ( Const UNI_Get ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  )    ( eqn ( IVar ( Para ''UniMsg_proc'' iRule1) )   (Const iRule2))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_Get_Put1VsInv71:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Global ''NakcMsg_Cmd'') )  ( Const NAKC_Nakc ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_Get_Put2VsInv71:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutXVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceHomeShrVldVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceShrVldVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_WbVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_GetX1VsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX2VsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX1VsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX2VsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX3VsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX4VsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_Get_GetVsInv71:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv71 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_Get_PutVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_PutXVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_ReplaceVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Remote_GetVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetXVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_PutXVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_ReplaceVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv71:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv71 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv71:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv71 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  end

theory flash73Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_InvVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1VsInv73:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_1_HomeVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_InvAck_2VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_GetXVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak1VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak2VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_Nak3VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX1VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX2VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX3VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX4VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX5VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX6VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX7VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8VsInv73:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX8_homeVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX9VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10VsInv73:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX10_homeVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_GetX_PutX11VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_GetVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak1VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak2VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Nak3VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put1VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put2VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_Get_Put3VsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Local_PutVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Local_PutXAcksDoneVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_NakVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Nak_ClearVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_Nak_HomeVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_NakVsInv73:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_GetX_Nak_HomeVsInv73:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_PutXVsInv73:  
  (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv73:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak1VsInv73:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_Remote_Get_Nak2VsInv73:  
    (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1 a2 a3,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_Get_Put1VsInv73:  
  (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Get ))    ( eqn ( IVar ( Global ''ShWbMsg_Cmd'') )  ( Const SHWB_ShWb ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_Get_Put2VsInv73:  
  (*Rule2VsPInv0*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iRule2) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_Put ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_Remote_PutVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_Remote_PutXVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ReplaceHomeVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceHomeShrVldVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma NI_ReplaceShrVldVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma NI_ShWbVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma NI_WbVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_GetX1VsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_GetX2VsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_GetX_PutX1VsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX2VsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX3VsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_GetX_PutX4VsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_Get_GetVsInv73:  
  (*Rule0VsPInv0*)
  shows  "invHoldForRule' s (inv73 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof -

  
      have "?P1 s"
         
        apply( auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_Get_PutVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_PutXVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Local_ReplaceVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  lemma PI_Remote_GetVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_GetXVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_PutXVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma PI_Remote_ReplaceVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreVsInv73:  
    (*Rule1VsPInv0*)
  assumes   a1:"iRule1 \<le> N" 

  shows  "invHoldForRule' s (inv73 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by (cut_tac a1,auto  )
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto
 qed
  lemma StoreHomeVsInv73:  
    (*Rule0VsPInv0*)
  
  shows  "invHoldForRule' s (inv73 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

   
      by( auto)
 
  end

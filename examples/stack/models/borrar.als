module SListInt32MySeq

open Integer32



one sig SListInt32MySeq  {}

abstract sig SListInt32Node {}



fact repOk {
  let next = QF.fnext_0+QF.bnext_0,
      thiz = QF.thiz_0,
      head = QF.head_0,
      value = QF.nodeValue_0,
      index = QF.index_0 |
  {
    // no cycles 
    all n: thiz.head.*next-null | { n !in n.next.*next and n.value != null }
    // compute indexes for nodes
    (thiz.head!=null => thiz.head.index = i320
                             and
                             (all n1,n2: thiz.head.*next-null | n1.next = n2 implies fun_java_primitive_integer_value_add[n1.index,i321] = n2.index)
    )
    
  }
}


pred sequence[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue] {
    all x: s.JavaPrimitiveIntegerValue | int32_prevs[x] in s.JavaPrimitiveIntegerValue 
}


fact {
    sequence[QF.thisType_1_0]
    sequence[QF.thisType_1_1]
}


fact abstraction {
  let thiz = QF.thiz_0,
      size = QF.size_0, 
      value = QF.nodeValue_0,
      index = QF.index_0,
      myseq = QF.thisType_1_1 |
  {
    (myseq_card[myseq, thiz.size])
    and
    (all i: myseq.JavaPrimitiveIntegerValue | i.myseq = index.i.value)
  }
}


fact {
  all a, b: JavaPrimitiveIntegerValue | 
    (a = b <=> pred_java_primitive_integer_value_eq[a,b]) 
--    ( pred_java_primitive_integer_value_eq[a,b]) 

}


//fact orderingAxiom1 
fact { 
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fnext_0,bf1=QF.bnext_0 | { 
-- forwardPlusBackwardAreFunctions
no ((ff1.univ) & (bf1.univ)) 
N0+N1+N2 = ff1.univ + bf1.univ 
--forwardIsIndeedForward 
entry in N0+null 
all n : entry.*ff1 - null | node_min[ff1.n] in node_prevs[n] 
all disj n1, n2 : entry.*ff1 - null | 
{ 
      ( some (ff1.n1 ) && some (ff1.n2 ) && node_min[ff1.n1 ] in 
      node_prevs[node_min[ff1.n2 ]] ) 
        implies n1 in node_prevs[n2] 
  } 
  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs)
  --prefixReachableForward 
    all x : entry.*(ff1) -null | node_prevs[x] in entry.*(ff1) 
} 
} 



fact fixReachable {all n : SListInt32Node | n !in (QF.thiz_0).(QF.head_0).*(QF.fnext_0) implies
		(
			n.(QF.nodeValue_0) = i320 and
            no n.(QF.index_0) and
			n.(QF.fnext_0) = null and
			no n.(QF.bnext_0)
		)
}


fun FReach[] :set (N0+N1+N2) {
    (QF.thiz_0).(QF.head_0).*(QF.fnext_0)-null
}

one sig N0,N1,N2 extends SListInt32Node {}




fact { QF.fnext_0 in N0->N1+N0->N2+N0->null+N1->N2+N1->null+N2->null }
fact { QF.bnext_0 in N0->N0+N1->N0+N1->N1+N2->N0+N2->N1+N2->N2 }


fact {
	(QF.index_0) in N0->i320+N0->i321+N0->i322+N0->null+N1->i320+N1->i321+N1->i322+N1->null+N2->i320+N2->i321+N2->i322+N2->null
}


fact {
	(QF.size_0) in SListInt32MySeq->i320+SListInt32MySeq->i321+SListInt32MySeq->i322+SListInt32MySeq->i323
}




// myseq definitions
fun int32_max[es: set (i320+i321+i322)] : lone (i320+i321+i322) {
 es - es.(
   i321->(i320)
   +
   i322->(i320+i321)
 )
}


fun int32_prevs[e: i320+i321+i322] :set (i320+i321+i322) {
 e.(
   i321->(i320)
   +
   i322->(i320+i321)
 )
}


pred myseq_card[s: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue, res: JavaPrimitiveIntegerValue] {
	let dom = s.JavaPrimitiveIntegerValue |
		(no dom and res = i320) or 
		(some dom and res = fun_java_primitive_integer_value_add[int32_max[dom],i321])
}


// end of myseq definitions


fun node_max[es: set (N0+N1+N2)] : lone (N0+N1+N2) {
 es - es.(
   N1->(N0)
   +
   N2->(N0+N1)
 )
}


fact mysize {
	let m = node_max[FReach[]-null], size = (QF.thiz_0).(QF.size_0) | 
	  (no m and size = i320) or 
	  (m = N0 and size = i321) or
	  (m = N1 and size = i322) or
	  (m = N2 and size = i323)

}


pred CanSatisfyInvariant[] {}
run CanSatisfyInvariant for 0 but exactly 1 SListInt32MySeq, exactly 3 SListInt32Node, 1 int, exactly 24  JavaPrimitiveIntegerValue

fun node_next[]: (N0+N1+N2) -> lone (N0+N1+N2) {
 N0->N1
 +
 N1->N2
}


fun node_prevs[e: N0+N1+N2] :set (N0+N1+N2) {
 e.(
   N1->(N0)
   +
   N2->(N0+N1)
 )
}


fun node_rprevs[e: N0+N1+N2] :set (N0+N1+N2) {
 e.(
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
 )
}


fun node_relprevs[] : (N0+N1+N2) -> set (N0+N1+N2) {
   N0->(N0)
   +
   N1->(N0+N1)
   +
   N2->(N0+N1+N2)
}


fun node_min[es: set (N0+N1+N2)] : lone (N0+N1+N2) {
 es - es.(
   N0->(N1+N2)
   +
   N1->(N2)
 )
}




fact{ 

//Bound for field QF.head_0: 
QF.head_0 in SListInt32MySeq->null + SListInt32MySeq->N0

//Bound for field QF.index_0: 
QF.index_0 in N0->i320 + N1->i321 + N2->i322

//Bound for field QF.fnext_0: 
QF.fnext_0 in N0->null + N0->N1 + N1->null + N1->N2 + N2->null

//Bound for field QF.bnext_0: 
QF.bnext_0 in none->none

//Bound for field QF.size_0: 
QF.size_0 in SListInt32MySeq->i320 + SListInt32MySeq->i321 + SListInt32MySeq->i322 + SListInt32MySeq->i323

}
fact{ 

//Bound for field QF.head_0: 
QF.head_0 in SListInt32MySeq->null + SListInt32MySeq->N0

//Bound for field QF.index_0: 
QF.index_0 in N0->i320 + N1->i321 + N2->i322

//Bound for field QF.fnext_0: 
QF.fnext_0 in N0->null + N0->N1 + N1->null + N1->N2 + N2->null

//Bound for field QF.bnext_0: 
QF.bnext_0 in none->none

//Bound for field QF.size_0: 
QF.size_0 in SListInt32MySeq->i320 + SListInt32MySeq->i321 + SListInt32MySeq->i322 + SListInt32MySeq->i323

}






one sig QF {intJ_1_0:JavaPrimitiveIntegerValue,intJ_1_1:JavaPrimitiveIntegerValue,intJ_2_0:JavaPrimitiveIntegerValue,intJ_2_1:JavaPrimitiveIntegerValue,return_intJ_1_1:JavaPrimitiveIntegerValue,return_intJ_2_1:JavaPrimitiveIntegerValue,return_bool_1:boolean,
  thisType_1_0: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thisType_1_1: JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  thiz_0:      one SListInt32MySeq,
  head_0:      SListInt32MySeq ->one(SListInt32Node+null),
  nodeValue_0: SListInt32Node ->one(JavaPrimitiveIntegerValue+null),
  index_0: SListInt32Node -> lone JavaPrimitiveIntegerValue,
  fnext_0:     SListInt32Node ->lone(SListInt32Node+null),
  bnext_0:     SListInt32Node ->lone(SListInt32Node+null),
  size_0:      SListInt32MySeq ->one JavaPrimitiveIntegerValue,
}

one sig null{}



pred postcondition_Lista_indexOf
[
  elem: JavaPrimitiveIntegerValue,
  values:JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  values':JavaPrimitiveIntegerValue->lone JavaPrimitiveIntegerValue,
  ret:JavaPrimitiveIntegerValue
] {
    sequence[values] and values'=values and
    ( ((no values.elem)  and pred_java_primitive_integer_value_eq[i320,ret]) 

or 
    (not(no values.elem) and (some min:values.elem | 
                                    (all e:values.elem | pred_java_primitive_integer_value_lte[min,e]) and 
				      pred_java_primitive_integer_value_eq[min,ret])) 

)
}





pred precondition_Lista_indexOf[]{}


pred aver[]{ precondition_Lista_indexOf[] and  postcondition_Lista_indexOf[QF.intJ_1_0,QF.thisType_1_0,QF.thisType_1_1,QF.return_intJ_1_1] }














run aver 








fact{QF.thisType_1_0 in ( i320->i323)+( i321->i321)+( i322->i323) and ( i320->i323)+( i321->i321)+( i322->i323) in QF.thisType_1_0}
fact{QF.intJ_1_0=i323 }
//fact {QF.intJ_2_0=i321}

one sig i320 extends JavaPrimitiveIntegerValue{}
one sig i321 extends JavaPrimitiveIntegerValue{}

one sig i322 extends JavaPrimitiveIntegerValue{}
one sig i323 extends JavaPrimitiveIntegerValue{}

one sig i32m1 extends JavaPrimitiveIntegerValue{}


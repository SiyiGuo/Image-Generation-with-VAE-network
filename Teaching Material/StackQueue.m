(* ::Package:: *)

(* :Title: StackQueue.m -- $Revision: 1.7 $ $Date: 2016/12/28 19:48:20 $ $Author: Bob $ *)

(* :Context: StackQueue` *)

(* :Author: Robert B. Nachbar *)

(* :Summary:
*)

(* :Copyright: \[Copyright] 2015 Robert Nachbar *)

(* :Package Version: $Revision: 1.7 $ *)

(* :Mathematica Version: 11.1 *)

(* :History:
*)

(* :Keywords: 
*)

(* :Sources:
*)

(* :Warnings:
   <description of global effects, incompatibilities>
*)

(* :Limitations:
   <special cases not handled, known problems>
*)

(* :Discussion:
   <description of algorithm, information for experts>
*)

(* :Requirements:
*)

(* :Examples:
   <sample input that demonstrates the features of this package>
*)

Print["StackQueue.m, $Revision: 1.7 $).\n"<>
	"\tDirect queries to Robert Nachbar, rnachbar@wolfram.com."] ;

(* set up the package context, including public imports *)

BeginPackage["StackQueue`"]
ClearAll[Evaluate[Context[]<>"*"]]

(* usage messages for the exported functions and the context itself *)

StackQueue::usage = "StackQueue.m is a package that provides efficient stack and queue functions."


InitializeStack::usage = "InitializeStack[stack] initializes a stack structure \
and associates it with the expression stack. \
The argument stack must be an expression without OwnValues or DownValues."

EmptyStackQ::usage = "EmptyStackQ[stack] returns True if stack is empty and False otherwise."

Push::usage = "Push[stack, expr] pushes expr onto the top of stack."

Pop::usage = "Pop[stack] removes the topmost expression from stack and returns it."

ClearStack::usage = "ClearStack[stack] clears the memory associate with stack."; 

PrintStack::usage = "PrintStack[stack] prints each element of stack from top to bottom."

FetchStack::usage = "FetchStack[stack] returns the elements of stack from bottom to top in a List."


InitializeQueue::usage = "InitializeQueue[queue] initializes a queue structure \
and associates it with the expression queue. The queue is treated as a double ended queue, \
with Enqueue added elements at the back and Requeue added elements at the front.\
The argument queue must be an expression without OwnValues or DownValues."

EmptyQueueQ::usage = "EmptyQueueQ[queue] returns True if queue is empty and False otherwise."

Enqueue::usage = "Enqueue[queue, expr] appends expr onto the back of queue."

Dequeue::usage = "Dequeue[queue] removes the first expression from queue and returns it."

Requeue::usage = "Requeue[queue, expr] prepends expr onto the front of queue."

ClearQueue::usage = "ClearQueue[queue] clears the memory associate with queue."; 

PrintQueue::usage = "PrintQueue[queue] prints each element of queue from front to back."


InitializeList::usage = "InitializeList[list] initializes a list structure \
and associates it with the expression list. Elements are added to the end and never removed. \
Elements can be copied out by position. \
The argument list must be an expression without OwnValues or DownValues."

InsertList::usage = "InsertList[list, expr] inserts expr at the end of list."; 

PartList::usage = "PartList[list, i] returns the ith element of list."

LengthList::usage = "LengthList[list] returns the number of elements in list."

ClearList::usage = "ClearList[list] clears the memory associate with list."; 

FetchList::usage = "FetchList[list] returns the elements of list from first to last in a List."

PrintList::usage = "PrintList[list] prints each element of list from first to last."


(* error messages for the exported objects *)

General::empty = "`1` has length 0 and no `2` element."

General::stack = "`1` is not a stack."

General::queue = "`1` is not a queue."

General::list = "`1` is not a list."


Begin["`Private`"]    (* begin the private context (implementation part) *)
ClearAll[Evaluate[Context[]<>"*"]]

(*
Needs[]    (* read in any hidden imports *)
*)

(* unprotect any system functions for which definitions will be made *)

protected = Unprotect[]

(* definition of auxiliary functions and local (static) variables *)

$stackList = <| |>

$queueList = {}

$listList = <| |>

(* definition of the exported functions *)

Attributes[InitializeStack] = {HoldFirst};

InitializeStack[stack_] := 
	With[{key=ToString[HoldForm[stack]]}, 
		Switch[$stackList[key], 
			_Missing, 
				AppendTo[$stackList, key -> {}], 
			_, 
				$stackList[key] = {}
			]; 
		]

Attributes[EmptyStackQ] = {HoldFirst};

f : EmptyStackQ[stack_] := 
	With[{s=$stackList[ToString[HoldForm[stack]]]}, 
		Switch[s, 
			_Missing, 
				Message[EmptyStackQ::stack, HoldForm[stack]]; 
				Return[Unevaluated@f], 
			_, 
				s == {}
			]
		]

Attributes[Push] = {HoldFirst};

f : Push[stack_, x_] := 
	With[{s=$stackList[ToString[HoldForm[stack]]]}, 
		Switch[s, 
			_Missing, 
				Message[Push::stack, HoldForm[stack]]; 
				Return[HoldForm@f], 
			_, 
				$stackList[ToString[HoldForm[stack]]] = {x, s};
			]
		]

Attributes[Pop] = {HoldFirst};

f : Pop[stack_] := 
	With[{s=$stackList[ToString[HoldForm[stack]]]}, 
		Switch[s, 
			_Missing, 
				Message[Pop::stack, HoldForm[stack]]; 
				Return[HoldForm@f], 
			_, 
				If[EmptyStackQ[stack], 
					Message[Pop::empty, stack, "top"]; 
					Return[HoldForm[f]], 
				  (* else *)
					$stackList[ToString[HoldForm[stack]]] = Last[s]; 
					First[s]
					]
			]
		]

Attributes[ClearStack] = {HoldFirst};

f : ClearStack[stack_] := 
	With[{key=ToString[HoldForm[stack]]}, 
		Switch[$stackList[key], 
			_Missing, 
				Message[ClearStack::stack, HoldForm[stack]]; 
				Return[HoldForm[f]], 
			_, 
				$stackList = Delete[$stackList, Key[key]]; 
			]; 
		]

Attributes[PrintStack] = {HoldFirst};

f : PrintStack[stack_] := 
	With[{s=$stackList[ToString[HoldForm[stack]]]}, 
		Switch[s, 
			_Missing, 
				Message[PrintStack::stack, HoldForm[stack]]; 
				Return[HoldForm@f], 
			_, 
				printStack[s]
			]
		]
printStack[{top_, bottom_}] := (Print[top]; printStack[bottom])
printStack[{}] := Null

Attributes[FetchStack] = {HoldFirst};

f : FetchStack[stack_] := 
	Module[{s=$stackList[ToString[HoldForm[stack]]], fetchStack, list, $l}, 
		fetchStack[{top_, bottom_}] := (list = $l[top, list]; fetchStack[bottom]); 
		fetchStack[{}] := List @@ Flatten @ list; 
		list = $l[]; 
		Switch[s, 
			_Missing, 
				Message[FetchStack::stack, HoldForm[stack]]; 
				Return[HoldForm@f], 
			_, 
				fetchStack[s]
			]
		]


Attributes[InitializeQueue] = {HoldFirst};

InitializeQueue[queue_] := (
	If[FreeQ[$queueList, queue], AppendTo[$queueList, queue]]; 
	InitializeStack[queue[front]];
	InitializeStack[queue[back]];
	)

Attributes[ClearQueue] = {HoldFirst};

ClearQueue[queue_] /; MemberQ[$queueList, queue] || 
	Message[ClearQueue::queue, queue] := (
	ClearStack[queue[front]]; 
	ClearStack[queue[back]]; 
	$queueList = DeleteCases[$queueList, queue];
	)

Attributes[EmptyQueueQ] = {HoldFirst};

EmptyQueueQ[queue_] /; MemberQ[$queueList, queue] || 
	Message[EmptyQueueQ::queue, queue] := 
	EmptyStackQ[queue[front]] && EmptyStackQ[queue[back]]

Attributes[Enqueue] = {HoldFirst};

Enqueue[queue_, x_] /; MemberQ[$queueList, queue] || 
	Message[Enqueue::queue, queue] := Push[queue[back], x]

Attributes[Dequeue] = {HoldFirst};

Dequeue[queue_] /; (MemberQ[$queueList, queue] || 
	TrueQ[Message[Dequeue::queue, queue]]) && 
	(!EmptyQueueQ[queue] || Message[Dequeue::empty, queue, "front"]) := 
	(If[EmptyStackQ[queue[front]], While[!EmptyStackQ[queue[back]], 
		Push[queue[front], Pop[queue[back]]]
		]];
    Pop[queue[front]])

Attributes[Requeue] = {HoldFirst};

Requeue[queue_, x_] /; MemberQ[$queueList, queue] || 
	Message[Requeue::queue, queue] := 
	(If[EmptyStackQ[queue[front]], While[!EmptyStackQ[queue[back]], 
		Push[queue[front], Pop[queue[back]]]
		]];
    Push[queue[front], x])

Attributes[PrintQueue] = {HoldFirst};

PrintQueue[queue_] /; (MemberQ[$queueList, queue] || 
	Message[PrintQueue::queue, queue]) && 
	(!EmptyQueueQ[queue] || Message[PrintQueue::empty, queue, "first"]) := 
	Module[{temp}, 
		If[!EmptyStackQ[queue[front]], 
			PrintStack[queue[front]]
			];
		If[!EmptyStackQ[queue[back]], 
			InitializeStack[temp]; 
			While[!EmptyStackQ[queue[back]], 
				Push[temp, Pop[queue[back]]]
				]; 
			PrintStack[temp]; 
			While[!EmptyStackQ[temp], 
				Push[queue[back], Pop[temp]]
				]
			];
		]


Attributes[InitializeList] = {HoldFirst};

InitializeList[list_] := 
	With[{s=$listList[ToString[HoldForm[list]]]}, 
		Switch[s, 
			_Missing, 
				AppendTo[$listList, ToString[HoldForm[list]] -> {Unique[list], 0}], 
			_, 
				ClearAll[s[[1]]]; 
				$listList[ToString[HoldForm[list]]] = {Unique[list], 0}
			]; 
		]

Attributes[LengthList] = {HoldFirst};

f : LengthList[list_] := 
	With[{s=$listList[ToString[HoldForm[list]]]}, 
		Switch[s, 
			_Missing, 
				Message[LengthList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				s[[2]]
			]
		]

Attributes[InsertList] = {HoldFirst};

f : InsertList[list_, x_] := 
	Module[{key=ToString[HoldForm[list]], s}, 
		Switch[s=$listList[key], 
			_Missing, 
				Message[InsertList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				With[{l=s[[1]], n=s[[2]]+1}, 
					l[n] = x; 
					$listList[key] = {l, n}; 
					]
			]
		]

Attributes[PartList] = {HoldFirst};

f : PartList[list_, i_Integer] := 
	With[{s=$listList[ToString[HoldForm[list]]]}, 
		Switch[s, 
			_Missing, 
				Message[PartList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				If[1 <= i <= s[[2]], 
					s[[1]][i], 
				  (* else *)
					Message[PartList::partw, i, HoldForm[list]]; 
					Null
					]
			]
		]

Attributes[FetchList] = {HoldFirst};

f : FetchList[list_] := 
	With[{s=$listList[ToString[HoldForm[list]]]}, 
		Switch[s, 
			_Missing, 
				Message[FetchList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				Table[s[[1]][i], {i, s[[2]]}]
			]
		]

Attributes[ClearList] = {HoldFirst};

f : ClearList[list_] := 
	Module[{key=ToString[HoldForm[list]], s}, 
		Switch[s=$listList[key], 
			_Missing, 
				Message[ClearList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				ClearAll[Evaluate @ s[[1]]]; 
				$listList = Delete[$listList, Key[key]];
			]
		]

Attributes[PrintList] = {HoldFirst};

f : PrintList[list_] := 
	With[{s=$listList[ToString[HoldForm[list]]]}, 
		Switch[s, 
			_Missing, 
				Message[PrintList::list, HoldForm[list]]; 
				Return[HoldForm@f], 
			_, 
				Do[Print[s[[1]][i]], {i, s[[2]]}]
			]
		]



(* definitions for system functions *)

Protect[ Evaluate[protected] ]     (* restore protection of system symbols *)

End[ ]         (* end the private context *)

(*
Protect[]    (* protect exported symbols *)
*)

EndPackage[ ]  (* end the package context *)

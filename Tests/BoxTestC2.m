// This file is generated by running
//    magma -b type:=C2 BoxTestGenerator.m
// Do not edit it by hand.

if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;SetColumns(0);
AttachSpec("ASLoc.spec");

// Test C~2
W := CoxeterGroup(GrpFPCox, CartanMatrix("C~2"));
assert EltToParam(W ! [ IntegerRing() | ]) eq \[ 0, 0, 0 ];
assert ParamToElt(W, \[ 0, 0, 0 ]) eq W ! [ IntegerRing() | ];
assert EltToParam(W ! \[ 3 ]) eq \[ 0, 0, 1 ];
assert ParamToElt(W, \[ 0, 0, 1 ]) eq W ! \[ 3 ];
assert EltToParam(W ! \[ 3, 1 ]) eq \[ 0, 0, 2 ];
assert ParamToElt(W, \[ 0, 0, 2 ]) eq W ! \[ 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2 ]) eq \[ 0, 0, 3 ];
assert ParamToElt(W, \[ 0, 0, 3 ]) eq W ! \[ 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 3 ]) eq \[ 0, 1, 0 ];
assert ParamToElt(W, \[ 0, 1, 0 ]) eq W ! \[ 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1 ]) eq \[ 1, 0, 0 ];
assert ParamToElt(W, \[ 1, 0, 0 ]) eq W ! \[ 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3 ]) eq \[ 0, 1, 1 ];
assert ParamToElt(W, \[ 0, 1, 1 ]) eq W ! \[ 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3 ]) eq \[ 1, 0, 1 ];
assert ParamToElt(W, \[ 1, 0, 1 ]) eq W ! \[ 3, 1, 2, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1 ]) eq \[ 0, 1, 2 ];
assert ParamToElt(W, \[ 0, 1, 2 ]) eq W ! \[ 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1 ]) eq \[ 1, 0, 2 ];
assert ParamToElt(W, \[ 1, 0, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 2, 0 ];
assert ParamToElt(W, \[ 0, 2, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 1, 3 ];
assert ParamToElt(W, \[ 0, 1, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2 ]) eq \[ 1, 0, 3 ];
assert ParamToElt(W, \[ 1, 0, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 3 ]) eq \[ 1, 1, 0 ];
assert ParamToElt(W, \[ 1, 1, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 2, 1 ];
assert ParamToElt(W, \[ 0, 2, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1 ]) eq \[ 2, 0, 0 ];
assert ParamToElt(W, \[ 2, 0, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3 ]) eq \[ 1, 1, 1 ];
assert ParamToElt(W, \[ 1, 1, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 2, 2 ];
assert ParamToElt(W, \[ 0, 2, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3 ]) eq \[ 2, 0, 1 ];
assert ParamToElt(W, \[ 2, 0, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1 ]) eq \[ 1, 1, 2 ];
assert ParamToElt(W, \[ 1, 1, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 2, 3 ];
assert ParamToElt(W, \[ 0, 2, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 3, 0 ];
assert ParamToElt(W, \[ 0, 3, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ]) eq \[ 2, 0, 2 ];
assert ParamToElt(W, \[ 2, 0, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 2, 0 ];
assert ParamToElt(W, \[ 1, 2, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ]) eq \[ 1, 1, 3 ];
assert ParamToElt(W, \[ 1, 1, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 3, 1 ];
assert ParamToElt(W, \[ 0, 3, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ]) eq \[ 2, 0, 3 ];
assert ParamToElt(W, \[ 2, 0, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ]) eq \[ 2, 1, 0 ];
assert ParamToElt(W, \[ 2, 1, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 1, 2, 1 ];
assert ParamToElt(W, \[ 1, 2, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 3, 2 ];
assert ParamToElt(W, \[ 0, 3, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ]) eq \[ 3, 0, 0 ];
assert ParamToElt(W, \[ 3, 0, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ]) eq \[ 2, 1, 1 ];
assert ParamToElt(W, \[ 2, 1, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 1, 2, 2 ];
assert ParamToElt(W, \[ 1, 2, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 4, 0 ];
assert ParamToElt(W, \[ 0, 4, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 3, 3 ];
assert ParamToElt(W, \[ 0, 3, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ]) eq \[ 3, 0, 1 ];
assert ParamToElt(W, \[ 3, 0, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ]) eq \[ 2, 1, 2 ];
assert ParamToElt(W, \[ 2, 1, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 2, 3 ];
assert ParamToElt(W, \[ 1, 2, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 1, 3, 0 ];
assert ParamToElt(W, \[ 1, 3, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 4, 1 ];
assert ParamToElt(W, \[ 0, 4, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ]) eq \[ 3, 0, 2 ];
assert ParamToElt(W, \[ 3, 0, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ]) eq \[ 2, 2, 0 ];
assert ParamToElt(W, \[ 2, 2, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ]) eq \[ 2, 1, 3 ];
assert ParamToElt(W, \[ 2, 1, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 1, 3, 1 ];
assert ParamToElt(W, \[ 1, 3, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 4, 2 ];
assert ParamToElt(W, \[ 0, 4, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ]) eq \[ 3, 0, 3 ];
assert ParamToElt(W, \[ 3, 0, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ]) eq \[ 3, 1, 0 ];
assert ParamToElt(W, \[ 3, 1, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 2, 2, 1 ];
assert ParamToElt(W, \[ 2, 2, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 1, 3, 2 ];
assert ParamToElt(W, \[ 1, 3, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 4, 3 ];
assert ParamToElt(W, \[ 0, 4, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 5, 0 ];
assert ParamToElt(W, \[ 0, 5, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ]) eq \[ 4, 0, 0 ];
assert ParamToElt(W, \[ 4, 0, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ]) eq \[ 3, 1, 1 ];
assert ParamToElt(W, \[ 3, 1, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 2, 2, 2 ];
assert ParamToElt(W, \[ 2, 2, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 4, 0 ];
assert ParamToElt(W, \[ 1, 4, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 1, 3, 3 ];
assert ParamToElt(W, \[ 1, 3, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 5, 1 ];
assert ParamToElt(W, \[ 0, 5, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ]) eq \[ 4, 0, 1 ];
assert ParamToElt(W, \[ 4, 0, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ]) eq \[ 3, 1, 2 ];
assert ParamToElt(W, \[ 3, 1, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 2, 2, 3 ];
assert ParamToElt(W, \[ 2, 2, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 2, 3, 0 ];
assert ParamToElt(W, \[ 2, 3, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 1, 4, 1 ];
assert ParamToElt(W, \[ 1, 4, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 5, 2 ];
assert ParamToElt(W, \[ 0, 5, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ]) eq \[ 4, 0, 2 ];
assert ParamToElt(W, \[ 4, 0, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ]) eq \[ 3, 2, 0 ];
assert ParamToElt(W, \[ 3, 2, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ]) eq \[ 3, 1, 3 ];
assert ParamToElt(W, \[ 3, 1, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 2, 3, 1 ];
assert ParamToElt(W, \[ 2, 3, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 1, 4, 2 ];
assert ParamToElt(W, \[ 1, 4, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 6, 0 ];
assert ParamToElt(W, \[ 0, 6, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 5, 3 ];
assert ParamToElt(W, \[ 0, 5, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ]) eq \[ 4, 0, 3 ];
assert ParamToElt(W, \[ 4, 0, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ]) eq \[ 4, 1, 0 ];
assert ParamToElt(W, \[ 4, 1, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 3, 2, 1 ];
assert ParamToElt(W, \[ 3, 2, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 2, 3, 2 ];
assert ParamToElt(W, \[ 2, 3, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 4, 3 ];
assert ParamToElt(W, \[ 1, 4, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 1, 5, 0 ];
assert ParamToElt(W, \[ 1, 5, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 6, 1 ];
assert ParamToElt(W, \[ 0, 6, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ]) eq \[ 5, 0, 0 ];
assert ParamToElt(W, \[ 5, 0, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ]) eq \[ 4, 1, 1 ];
assert ParamToElt(W, \[ 4, 1, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 3, 2, 2 ];
assert ParamToElt(W, \[ 3, 2, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 2, 4, 0 ];
assert ParamToElt(W, \[ 2, 4, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 2, 3, 3 ];
assert ParamToElt(W, \[ 2, 3, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 1, 5, 1 ];
assert ParamToElt(W, \[ 1, 5, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 6, 2 ];
assert ParamToElt(W, \[ 0, 6, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ]) eq \[ 5, 0, 1 ];
assert ParamToElt(W, \[ 5, 0, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ]) eq \[ 4, 1, 2 ];
assert ParamToElt(W, \[ 4, 1, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 3, 2, 3 ];
assert ParamToElt(W, \[ 3, 2, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 3, 3, 0 ];
assert ParamToElt(W, \[ 3, 3, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 2, 4, 1 ];
assert ParamToElt(W, \[ 2, 4, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 1, 5, 2 ];
assert ParamToElt(W, \[ 1, 5, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 6, 3 ];
assert ParamToElt(W, \[ 0, 6, 3 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 0, 7, 0 ];
assert ParamToElt(W, \[ 0, 7, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ]) eq \[ 5, 0, 2 ];
assert ParamToElt(W, \[ 5, 0, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ]) eq \[ 4, 2, 0 ];
assert ParamToElt(W, \[ 4, 2, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ]) eq \[ 4, 1, 3 ];
assert ParamToElt(W, \[ 4, 1, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 3, 3, 1 ];
assert ParamToElt(W, \[ 3, 3, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 2, 4, 2 ];
assert ParamToElt(W, \[ 2, 4, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 6, 0 ];
assert ParamToElt(W, \[ 1, 6, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 1, 5, 3 ];
assert ParamToElt(W, \[ 1, 5, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 0, 7, 1 ];
assert ParamToElt(W, \[ 0, 7, 1 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ]) eq \[ 5, 0, 3 ];
assert ParamToElt(W, \[ 5, 0, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ]) eq \[ 5, 1, 0 ];
assert ParamToElt(W, \[ 5, 1, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 4, 2, 1 ];
assert ParamToElt(W, \[ 4, 2, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 3, 3, 2 ];
assert ParamToElt(W, \[ 3, 3, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 2, 4, 3 ];
assert ParamToElt(W, \[ 2, 4, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 2, 5, 0 ];
assert ParamToElt(W, \[ 2, 5, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 1, 6, 1 ];
assert ParamToElt(W, \[ 1, 6, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 0, 7, 2 ];
assert ParamToElt(W, \[ 0, 7, 2 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ]) eq \[ 6, 0, 0 ];
assert ParamToElt(W, \[ 6, 0, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ]) eq \[ 5, 1, 1 ];
assert ParamToElt(W, \[ 5, 1, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 4, 2, 2 ];
assert ParamToElt(W, \[ 4, 2, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 3, 4, 0 ];
assert ParamToElt(W, \[ 3, 4, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 3, 3, 3 ];
assert ParamToElt(W, \[ 3, 3, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 2, 5, 1 ];
assert ParamToElt(W, \[ 2, 5, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 1, 6, 2 ];
assert ParamToElt(W, \[ 1, 6, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 0, 8, 0 ];
assert ParamToElt(W, \[ 0, 8, 0 ]) eq W ! \[ 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ]) eq \[ 5, 1, 2 ];
assert ParamToElt(W, \[ 5, 1, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 4, 2, 3 ];
assert ParamToElt(W, \[ 4, 2, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ]) eq \[ 4, 3, 0 ];
assert ParamToElt(W, \[ 4, 3, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 3, 4, 1 ];
assert ParamToElt(W, \[ 3, 4, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 2, 5, 2 ];
assert ParamToElt(W, \[ 2, 5, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 1, 6, 3 ];
assert ParamToElt(W, \[ 1, 6, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ]) eq \[ 5, 2, 0 ];
assert ParamToElt(W, \[ 5, 2, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ]) eq \[ 4, 3, 1 ];
assert ParamToElt(W, \[ 4, 3, 1 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 3, 4, 2 ];
assert ParamToElt(W, \[ 3, 4, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 2, 6, 0 ];
assert ParamToElt(W, \[ 2, 6, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ]) eq \[ 4, 3, 2 ];
assert ParamToElt(W, \[ 4, 3, 2 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 3, 4, 3 ];
assert ParamToElt(W, \[ 3, 4, 3 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];
assert EltToParam(W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ]) eq \[ 4, 4, 0 ];
assert ParamToElt(W, \[ 4, 4, 0 ]) eq W ! \[ 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2 ];

quit;
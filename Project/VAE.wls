#!/usr/bin/env wolframscript
(* ::Package:: *)

trainingData = First/@ResourceData["MNIST", "TrainingData"]\:ff1b
batchsize = 64;
dim = 28;
randomDim = 10;

encoder = 
 NetChain[{128, Ramp, 128, Ramp, 28*28, LogisticSigmoid, 
   ReshapeLayer[{1, 28, 28}]}, "Input" -> randomDim];
decoder = 
 NetChain[{128, Ramp, 128, Ramp, 128, Ramp, 1}, 
  "Input" -> {1, 28, 28}];

wganNet = 
 NetInitialize[
  NetGraph[<|"gen" -> generator, 
    "discrimop" -> NetMapOperator[discriminator], 
    "cat" -> CatenateLayer[], 
    "reshape" -> ReshapeLayer[{2, 1, 28, 28}], 
    "flat" -> FlattenLayer[], "total" -> SummationLayer[], 
    "scale" -> ConstantTimesLayer["Scaling" -> {-1, 1}]|>, 
     {
     NetPort["random"] ->"gen" -> "cat", NetPort["Input"] -> "cat", 
    "cat" ->"reshape" -> "discrimop" -> "flat" -> "scale" -> "total"
     }, 
     "Input"->NetEncoder[{"Image", {dim,dim}, "Grayscale"}
	]
];
   
vae = NetChain[
	Join[encoder, decoder],
	",
	"Output "\[Rule]NetDecoder[{"Image ", "Grayscale "}]
]

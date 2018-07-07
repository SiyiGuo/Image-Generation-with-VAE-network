#!/usr/bin/env wolframscript
(* ::Package:: *)
Echo["Start working"]
nlatent = 8;
lrelu = ElementwiseLayer[Max[Ramp[#], #*0.3]&];


Echo["Encoder"]
(*encoder*)
encoder = NetChain[{
ConvolutionLayer[64, 4, "Stride"->2, "PaddingSize"->2],
lrelu,
DropoutLayer[],
ConvolutionLayer[64, 4, "Stride"->2, "PaddingSize"->2],
lrelu,
DropoutLayer[],
ConvolutionLayer[64, 4, "Stride"->1, "PaddingSize"->2],
lrelu,
DropoutLayer[],
FlattenLayer[]
}];
(*Middle Z*)
mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];
(*decoder*)
decoder = NetChain[{
25,
lrelu,
49, 
lrelu,
ReshapeLayer[{1,7,7}],
DeconvolutionLayer[64, 4, "Stride"->2,"PaddingSize"->2],
Ramp,
DropoutLayer[],
DeconvolutionLayer[64, 4, "Stride"->1,"PaddingSize"->2],
Ramp,
DropoutLayer[],
DeconvolutionLayer[64, 4, "Stride"->1,"PaddingSize"->2],
Ramp,
FlattenLayer[],
28*28,
LogisticSigmoid,
ReshapeLayer[{1,28,28}]
}];


(*Image Loss*)
(*Assume input is {1,28,28}*)
(*imageLoss =NetChain[{ThreadingLayer[#2-#1 &], ElementwiseLayer[#^2&], AggregationLayer[Total,1]}]*)
imageLoss = NetGraph[
  {ElementwiseLayer[-1*# &], TotalLayer[], ElementwiseLayer[#^2 &], 
   ReshapeLayer[{28, 28}], SummationLayer[]},
  {
   NetPort["inDec"] -> 1 -> 2,
   NetPort["inInput"] -> 2,
   2 -> 3 -> 4 -> 5
   }
  ];
(*Latent Loss*)
(*Assume input is {8}, {8}*)
latentLoss = NetGraph[
{ElementwiseLayer[-0.5*#&], TotalLayer[], ElementwiseLayer[-(#^2)&], ElementwiseLayer[-Exp[2*#]&], ElementwiseLayer[1+2*#&],SummationLayer[]},
{
NetPort["mn"]->3,
NetPort["sd"]->4,
NetPort["sd"]->5,
3->2,
4->2,
5->2,
2->6,
6->1
}
]
(*Loss*)

Echo["Initializing vaeNet"]
(*Further AssemBling*)
vaeNet = NetInitialize[NetGraph[
<|"enc"->encoder,
"mn"->mn,
"sd"-> sd,"expSd"->expSd,"sdEpsilon"->ThreadingLayer[Times],
"z"->TotalLayer[],
"dec"->decoder,
"imageLoss"->imageLoss,
"latentLoss"->latentLoss
|>,
{
NetPort["Input"]->"enc",
"enc"->"mn",
 "enc"->"sd", 
"sd"->"expSd","expSd"->"sdEpsilon", NetPort["random"] ->"sdEpsilon",
"mn"->"z", 
"sdEpsilon"->"z",
"z"->"dec",
"dec"->NetPort["Output"],
(*latent loss*)
"sd"->NetPort["latentLoss","sd"],
"mn"->NetPort["latentLoss","mn"],
(*image loss*)
"dec"->NetPort["imageLoss", "inDec"],
NetPort["Input"]->NetPort["imageLoss", "inInput"],
(*image loss8*)
"latentLoss"->NetPort["latentLoss"],
"imageLoss"->NetPort["imageLoss"]
},
"Output"->NetDecoder[{"Image", "Grayscale"}],
"Input"->NetEncoder[{"Image", {28,28}, "Grayscale"}]
]]


(*Training Data*)
Echo["Getting dataset"]
mnistDigits = First/@(RandomSample[ResourceData["MNIST"]]);
trainingData =<|"random"->RandomVariate[NormalDistribution[],{Length@mnistDigits,nlatent}],
"Input"->mnistDigits|>


dir = CreateDirectory[];
Echo[dir];

(*Training Process*)
Echo["Launching Training"]
ClearAll[trainedVae];
trainedVae = NetTrain[vaeNet, trainingData, 
LossFunction->{"latentLoss"->Scaled[1], "imageLoss"->Scaled[28*28]},
TrainingProgressCheckpointing->{"Directory", dir},
MaxTrainingRounds->1000,
TrainingProgressReporting->"Print",
Method->{"ADAM", "LearningRate"->0.0005},
TargetDevice->"GPU", BatchSize->64]
Export["2.wlnet", trainedVae]

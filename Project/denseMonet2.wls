#!/usr/bin/env wolframscript
(* ::Package:: *)

nlatent = 64;
width = 256;
convChannel = 64;
kernel = 8;


lrelu = ElementwiseLayer[Max[Ramp[#], #*0.3]&]
encoder = NetChain[{
ReshapeLayer[{3,width,width}],
ConvolutionLayer[convChannel, kernel, "Stride"->2, "PaddingSize"->2],
Tanh,
ConvolutionLayer[convChannel, kernel, "Stride"->2, "PaddingSize"->2],
Tanh,
FlattenLayer[],
576
}]



mn = LinearLayer[nlatent];
sd= NetChain[{LinearLayer[nlatent],ElementwiseLayer[#*0.5&]}];
expSd = ElementwiseLayer[Exp[#]&];
z =TotalLayer[];



decoder = NetChain[{
576,
Tanh,
768, 
Tanh,
ReshapeLayer[{3,16,16}],
DeconvolutionLayer[64, 4, "Stride"->2,"PaddingSize"->2],
Tanh,
DropoutLayer[],
DeconvolutionLayer[convChannel, 4, "Stride"->1,"PaddingSize"->2],
Tanh,
FlattenLayer[],
3*width,
Tanh,
3*width*width,
LogisticSigmoid,
ReshapeLayer[{3,width,width}]
}, "Input"->{nlatent}]



imageLoss = NetGraph[
{ElementwiseLayer[-1*# &, "Input"->{3,width,width}], TotalLayer[], ElementwiseLayer[#^2&], SummationLayer[]},
{
NetPort["inDec"]->1->2,
NetPort["inInput"]->2,
2->3->4
}
]



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


Echo["Before initializing the Net"]

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
"Output"->NetDecoder[{"Image", "RGB"}],
"Input"->NetEncoder[{"Image", {width, width}, "RGB"}]
]]


Echo["Getting image Path"]
imagePaths = Joine[
FileNames["*.jpg","DataMonet"],
FileNames["*.jpg","DataLandScape"],
FileNames["*.jpg", "DataCezanne"]
];
dataSets = Map[Import[#]&, imagePaths];
Echo[Length@dataSets]


trainingData =<|"random"->RandomVariate[NormalDistribution[],{Length@dataSets,nlatent}],
"Input"->dataSets|>;


dir = CreateDirectory[]
Echo[dir];
trainedVae = NetTrain[vaeNet, trainingData, LossFunction->{"latentLoss"->Scaled[1], "imageLoss"->Scaled[1]},
MaxTrainingRounds->2000,
TrainingProgressReporting->"Print",
Method->{"ADAM", "LearningRate"->0.00005},
TargetDevice->"GPU",
TrainingProgressCheckpointing->{"Directory", dir, "Interval"->Quantity[100, "Rounds"]},
 BatchSize->32];
Export["monetVae.wlnet", trainedVae];

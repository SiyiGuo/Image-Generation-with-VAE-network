Image Generation with Variational Auto Encoder

This project is about a network that can lean the pattern of the input image data and generate new images that follow the same pattern. The model is based on this paper [1], where the authors illustrated the idea of Variational Autoencoders. The value of Image data is represented as a multi-dimensional probability distribution. Each pixel value on the image is a point sampled from a probability distribution. For instance, a greyscale image of 28*28 resolution is a 784-dimension probability distribution. Variational Autoencoders maps the image’s high dimensional space into a lower dimension space, and can also recover the image data back to the high dimension from that lower dimension space. The model consists of three parts: the encoder layer, reparametrize layer and the decoder layer. 

See url: http://community.wolfram.com/groups/-/m/t/1379189?p_p_auth=JHNErmO4 for a full explaination of the project

[1] Doersch, C. (2016). Tutorial on variational autoencoders. arXiv preprint arXiv:1606.05908.

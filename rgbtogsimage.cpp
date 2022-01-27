/*
 This C++ code reads an RGB image, convert the RGB image to:
   1. grayscale image (as a matrix) 
   2. binary image as a matrix (stored in 'binaryimage.txt') as well as Coq definition  of the image (stored in 'coqbinaryimage.text')
   and generates Coq script ('proofofgsi.v').
*/

#include <stdint.h>
#include <iostream>
#include <string>
#include <fstream>

using std::string;

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"
#define STBI_MSC_SECURE_CRT
#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

int main() {
    int width, height, channels;
	int threshold = 100;
	string coqgsimage =  "[";
	string coqmatriximg = "[";
	string coqbinaryimage = "[";
	string imagename = " ";
	string binaryimage = "";
		
//Coq script
const char *coqscript = "(*Coq generated grayscale image*) \
\nDefinition gsimagecoq := createimage (rev coqmatriximg) (rows'-1) (cols'-1) (cols'-1). \
\n\n(*Coq generated binary image*)\n\
 Definition binimagecoq := thresholding gsimagecoq threshold.\n\n\
(*Proof that the tool generated gray image 'coqgsimage' and Coq generated image 'gsimagecoq' are the same.*) \n\
Lemma gsimage_eq: coqgsimage = gsimagecoq. \n\
 Proof. \n\
  unfold gsimage. \n\
  unfold gsimagecoq.  \n\
  simpl.    \n\
  reflexivity. \n\
Qed. \n\n\
(*Proof that the tool generated binary image 'coqbinaryimage' and Coq generated binary image 'binimagecoq' are the same.*)  \n\
 Lemma binimage_eq: coqbinaryimage = binimagecoq. \n\
 Proof. \n\
  unfold coqbinaryimage. \n\
  unfold binimagecoq.  \n\ unfold gsimagecoq. \n\
  simpl.    \n\
  reflexivity. \n\
Qed. \n\n\
Compute (thresholding coqgsimage 170). \n\n\
Compute gsimagecoq. (*creates gray scale image from coqmatriximg*) \n\n\
(*creates binary image in the threshold range*) \n\
Definition binaryimage := (thresholdrange coqgsimage 100 200). \n\n\
Compute (areasize binaryimage). \n\n\
Compute (runlength binaryimage). \n\n\
Compute (sumrunlen (runlength binaryimage))."; 
	
	std::cout<<"\n---- Enter valid image file name with ----\n\t";
	std::cin >> imagename;
	
	std::cout<<"\n---- Enter a threshould value between (0-255) ----\n\t";
	std::cin >> threshold;
    
    uint8_t* rgb_image = stbi_load(imagename.c_str(), &width, &height, &channels, 0); 
	
	//std::cout<<"\nLoaded image with a width of "<<width<<", a height of "<<height<<" and "<<channels<<"\n\n";
	
    int *rgbimagearray = new int[width*height*channels]; 
	int *grayimagearray = new int[width*height];
	 
	//populate the rgbimage int array
	for(int i=0; i<width*height*channels; i++) {
		rgbimagearray[i] = (int)(rgb_image[i]);
	}
	
	//populate grayimagearray (take average of the R,G,B channel values)
	int index=0;
	for(int i=0; i<width*height*channels; i += channels){
		grayimagearray[index++] = (rgbimagearray[i] + rgbimagearray[i+1] + rgbimagearray[i+2])/3;
	}
				
	if (rgb_image == NULL | threshold < 0 | threshold > 255) {
		if (rgb_image == NULL)
			std::cerr << "The image "<<imagename<<" could not be loaded. \n Please enter a valid image file name." <<std::endl;
		else std::cerr << "The threshold value "<<threshold<<" is out of range." <<std::endl;
	}
    else {

		//Create content of text files (binary image matrix and Coq binary image)
		int row = 0;
		for(int i=0; i<width*height; i++) {
			if (i!= 0 && i%width == 0) {
				row++;
				coqmatriximg = coqmatriximg + "\n";
				coqgsimage = coqgsimage + "\n";
				coqbinaryimage = coqbinaryimage + "\n";
				binaryimage = binaryimage + "\n";
			}
			coqmatriximg = coqmatriximg + std::to_string(grayimagearray[i])+";";
			coqgsimage = coqgsimage +"G{"+std::to_string(row)+","+std::to_string(i%width)+","+std::to_string(grayimagearray[i])+"};";	
			if (grayimagearray[i] <= threshold)  {
				binaryimage = binaryimage + "1" +" ";
				coqbinaryimage = coqbinaryimage +"B{"+std::to_string(row)+","+std::to_string(i%width)+","+"black"+"};";	
			} 
		    else { binaryimage = binaryimage + "0" +" ";
				   coqbinaryimage = coqbinaryimage +"B{"+std::to_string(row)+","+std::to_string(i%width)+","+"white"+"};";
			}
		}

		coqmatriximg[coqmatriximg.length() - 1] = ']';
		coqgsimage[coqgsimage.length() - 1] = ']';
		coqbinaryimage[coqbinaryimage.length() - 1] = ']';
		binaryimage[binaryimage.length() - 1] = '\0';
		
		coqgsimage = "Require Import binary_image_processing. \n\n(*Tool generated grayscale image matrix*)\nDefinition coqmatriximg := \n"+ coqmatriximg + ".\n\n" +
				  "(*Tool generated Coq definition of grayscale image*)\nDefinition coqgsimage := \n"+coqgsimage + ".\n\n"+
				   "(*Tool generated Coq definition of binary image*)\nDefinition coqbinaryimage := \n"+coqbinaryimage + ".\n\nDefinition rows' := "+std::to_string(height)+".\n\n" + 
				   "Definition cols' := "+std::to_string(width)+".\n\nDefinition threshold := "+std::to_string(threshold)+".\n\n" + coqscript;	
				   
		//writing the Coq gray scale image to a file
		std::ofstream out1("proofofgsi.v");		
		out1 << coqgsimage;
		out1.close();
		
		//writing the binary image to a file
		std::ofstream out2("binaryimage.txt");
		out2 << binaryimage;
		out2.close();
		
		//writing the binary image to a file
		std::ofstream out3("coqbinaryimage.txt");
		out3 << coqbinaryimage;
		out3.close();
		
		//stbi_image_free(gray_img);
 		stbi_image_free(rgb_image);
    }
	
	system("pause");
    return 0;
}
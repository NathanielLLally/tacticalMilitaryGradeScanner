#!/usr/bin/python
# Import required packages
import cv2 as cv
import cv2 as cv2
import pytesseract
import sys
import optparse
import subprocess
import os
import time
import threading
import queue
import signal
import re
from pathlib import Path
import numpy as np
import math
import inspect #pass frame to sig handler
from skimage.feature import hog
from imutils.object_detection import non_max_suppression
from PyQt5 import QtGui
from PyQt5 import QtCore
#from PyQt5.QtWidgets import QWidget, QApplication, QLabel, QVBoxLayout, QTable, QTableItem
from PyQt5.QtWidgets import * 
from PyQt5.QtGui import QPixmap
from PyQt5.QtCore import *
#pyqtSignal, pyqtSlot, Qt, QThread
import json
import webbrowser
import requests
import urllib
from ppretty import ppretty
import traceback

# TODO
#   MVP:
#      get web site price lookups happening then integrate into app
# 
#       if strippable chars are an issue, work in card dictionary detection before api call
#
#   resize image window - resize main image
#
#   re-eval tile size after all card shapes are identified
#     split output into per card regions based on tile
#     fine tune control, pause processing once matched per card
#
#   test for motion before processing text
#   get a binder sleave and cards for testing
#
#  perform price lookup on text, get title back, perform confidence on match
#   take title from price if confidence above X (n letter difference etc..)
#
#  stop processing those tiles upon match, leave title and prices on screen
#
page = 1

# Adaptive threshold levels
BKG_THRESH = 30
CARD_THRESH = 30

def stdout_reader(proc, q):
    for line in iter(proc.stdout.readline, b''):
        q.put(line.decode('utf-8'))

def stderr_reader(proc, q):
    for line in iter(proc.stderr.readline, b''):
        q.put(line.decode('utf-8'))

def handler(signum, frame):
    try:
        if (isinstance(proc, subprocess.Popen)):
            proc.terminate()
        sys.exit(app.exec_())
    except:
        pass
    sys.exit()

def nothing(*arg):
    pass

class VideoThread(QThread):
    change_pixmap_signal = pyqtSignal(np.ndarray)
    change_table_signal = pyqtSignal(dict)
    change_text_signal = pyqtSignal(dict)
    canny_lower_signal = pyqtSignal(int)
    canny_upper_signal = pyqtSignal(int)

    def __init__(self,vdev=0,lower=None, upper=None, debug=False):
        super().__init__()
        self._run_flag = True
        self.previous_frame = None #motion detection
        self.frame_count = 0
        self.vdev = vdev
        self.timeout = 5
        self.cardsByTile = {}
        self.scale_percent = 100 # percent of original size
        self.method="edge"
        self.debug = debug
        self.image_options = None
        self.cannyLower = lower
        self.cannyUpper = upper
        # load the pre-trained EAST text detector
        print("[INFO] loading EAST text detector...")
        self.net = cv.dnn.readNet("frozen_east_text_detection.pb")

    def tap(self, x,y):
            self.serial="0123456789ABCDEF"
            cmd = "adb -s %s shell input tap %s %s" % (self.serial,x * 2,y * 2)
            print(cmd)
            result = subprocess.run(cmd.split(), capture_output=True, text=True)
            print(result)
            return result

    def fast_east(self,image,min_confidence=0.5):
        orig = image.copy()
        (H, W) = image.shape[:2]

        # set the new width and height and then determine the ratio in change
        # for both the width and height
        (newW, newH) = (224, 64)
        rW = W / float(newW)
        rH = H / float(newH)

        # resize the image and grab the new image dimensions
        image = cv.resize(image, (newW, newH))
        (H, W) = image.shape[:2]

        # define the two output layer names for the EAST detector model that
        # we are interested -- the first is the output probabilities and the
        # second can be used to derive the bounding box coordinates of text
        layerNames = [
            "feature_fusion/Conv_7/Sigmoid",
            "feature_fusion/concat_3"]

        # construct a blob from the image and then perform a forward pass of
        # the model to obtain the two output layer sets
        blob = cv.dnn.blobFromImage(image, 1.0, (W, H),
            (123.68, 116.78, 103.94), swapRB=True, crop=False)
        start = time.time()
        self.net.setInput(blob)
        (scores, geometry) = self.net.forward(layerNames)
        end = time.time()

        # show timing information on text prediction
    #    print("[INFO] text detection took {:.6f} seconds".format(end - start))

        # grab the number of rows and columns from the scores volume, then
        # initialize our set of bounding box rectangles and corresponding
        # confidence scores
        (numRows, numCols) = scores.shape[2:4]
        rects = []
        confidences = []

        # loop over the number of rows
        for y in range(0, numRows):
            # extract the scores (probabilities), followed by the geometrical
            # data used to derive potential bounding box coordinates that
            # surround text
            scoresData = scores[0, 0, y]
            xData0 = geometry[0, 0, y]
            xData1 = geometry[0, 1, y]
            xData2 = geometry[0, 2, y]
            xData3 = geometry[0, 3, y]
            anglesData = geometry[0, 4, y]

            # loop over the number of columns
            for x in range(0, numCols):
                # if our score does not have sufficient probability, ignore it
                if scoresData[x] < min_confidence:
                    continue

                # compute the offset factor as our resulting feature maps will
                # be 4x smaller than the input image
                (offsetX, offsetY) = (x * 4.0, y * 4.0)

                # extract the rotation angle for the prediction and then
                # compute the sin and cosine
                angle = anglesData[x]
                cos = np.cos(angle)
                sin = np.sin(angle)

                # use the geometry volume to derive the width and height of
                # the bounding box
                h = xData0[x] + xData2[x]
                w = xData1[x] + xData3[x]

                # compute both the starting and ending (x, y)-coordinates for
                # the text prediction bounding box
                endX = int(offsetX + (cos * xData1[x]) + (sin * xData2[x])) 
                endY = int(offsetY - (sin * xData1[x]) + (cos * xData2[x]))
                startX = int(endX - w)
                startY = int(endY - h)

                # scale the bounding box coordinates based on the respective
                # ratios
                #startX = int(startX * rW)
                #startY = int(startY * rH)
                #endX = int(endX * rW) + 2
                #endY = int(endY * rH) + 2

                # add the bounding box coordinates and probability score to
                # our respective lists
                rects.append((startX, startY, endX, endY))
                confidences.append(scoresData[x])

        # apply non-maxima suppression to suppress weak, overlapping bounding
        # boxes
        boxes = non_max_suppression(np.array(rects), probs=confidences)

        rects = []
        for (startX, startY, endX, endY) in boxes:
            # scale the bounding box coordinates based on the respective
            # ratios
            startX = int(startX * rW)
            startY = int(startY * rH)
            endX = int(endX * rW) + 2
            endY = int(endY * rH) + 2

            rects.append((startX, startY, endX, endY))

        return rects

    # invert
    # correct skew 
    # crop top 
    # use fast east on title 
    # feed to tesseract
    #
    def process_card(self,crop,bounds,tilesize, page):
        #thresh
        # poi's 
        #tesseract
        words = []
        tconfs = []
        w = crop.shape[0]
        h = crop.shape[1]
        pro = 0
        if (h > w):
            pro = round(h / w, 2)
        else:
            pro = round(w / h,2)
    #    area = h * w
        #round

        #  if dimensions are within the size of 1 and 5 tiles
        #  proportion of L to W is within 1.3 to 1.5 (typical card)
        #  attempt a few methods for processing to OCR with tesseract
        #  return (text, confidence) of the method with highest confidence
        #  save all images used by page, tile, and type in pwd/cards
        #
        tile = self.get_tile(bounds[0], bounds[1], w, h, tilesize)
#        print(tile, pro, h, w)
        if ((h > self.tileH and h < self.tileH * self.tileRows) and
            (w > self.tileW and w < self.tileW * self.tileCols) and 
            (pro >= 1 and pro <= 1.6)):
    #bounding rect could be square with proportion of 1 if angled @ 45

            #  go for white text on darker background
            #
            crop = cv.bitwise_not(crop)

            #  correct skew

            # threshold the image, setting all foreground pixels to
            # 255 and all background pixels to 0
            thresh = cv.threshold(cv.cvtColor(crop,cv.COLOR_BGR2GRAY), 0, 255, cv.THRESH_BINARY | cv.THRESH_OTSU)[1]

      # Specify structure shape and kernel size.
        # Kernel size increases or decreases the area
        # of the rectangle to be detected.
        # A smaller value like (10, 10) will detect
        # each word instead of a sentence.
            rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (8, 8))

        # Applying dilation on the threshold image
            dilation = cv.dilate(thresh, rect_kernel, iterations=1)

        # Finding contours
            contours, hierarchy = cv.findContours(
                dilation, cv.RETR_EXTERNAL, cv.CHAIN_APPROX_NONE
                )

    #        cv.drawContours(t2, contours, 0, (0, 255, 0), 1)


            # grab the (x, y) coordinates of all pixel values that
            # are greater than zero, then use these coordinates to
            # compute a rotated bounding box that contains all
            # coordinates
            coords = np.column_stack(np.where(thresh > 0))
            crect = cv.minAreaRect(coords)
    #        box=cv.boxPoints(crect)
    #        box=np.int0(box)
    #        cv.drawContours(crop, [box], -1, (0, 255, 0), 1)

            angle = crect[-1]
            oangle = angle
            rw, rh = crect[1]
            # the `cv2.minAreaRect` function returns values in the
            # range [-90, 0); as the rectangle rotates clockwise the
            # returned angle trends to 0 -- in this special case we
            # need to add 90 degrees to the angle
            if angle < -45:
                angle = -(90 + angle)
            # otherwise, just take the inverse of the angle to make
            # it positive
            else:
                angle = -angle

            mangle = angle

            #https://stackoverflow.com/questions/15956124/minarearect-angles-unsure-about-the-angle-returned
            #
            if (rw > rh):
                pass
    #            angle+=180
            else:
                angle+=90
            

            # rotate the image to deskew it
            (h, w) = crop.shape[:2]
            center = (w // 2, h // 2)
            M = cv.getRotationMatrix2D(center, angle, 1.0)
            rotated = cv.warpAffine(crop, M, (w, h),
                flags=cv.INTER_CUBIC, borderMode=cv.BORDER_REPLICATE)

            title = rotated[0: int(h/27 * 5), 0: w]
            tshow = title.copy()

    #        cv.rectangle(img=tt2, pt1=(x, y), pt2=(x + w, y + h), color=(0, 255, 0), thickness=2)

            if (self.debug):
                cv.putText(crop, '%.4f' % (oangle),
                           (40, 40),
                           cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 1)
                cv.putText(crop, '%.4f' % (mangle),
                           (40, 80),
                           cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 1)
                cv.putText(crop, '%.4f' % (angle),
                           (40, 120),
                           cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 1)
                cv.putText(crop, 'w%d h%d' % (rw,rh),
                           (40, 160),
                           cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 1)

            boxes = self.fast_east(title)

            boxc = 0
            for box in sorted(boxes, key=lambda x: x[0]):
                boxc += 1
               
                (x, y, x2, y2) = box
    #                x, y, w, h = unscaled
                    #crop
     #               cardimage=orig[y: y + h, x : x + w]
    #            print("x[%d] y[%d] x2[%d] y2[%d]" % (x,y,x2,y2))
                img = title[y:y2,x:x2]

    #            if (img is None):
    #                print("Empty!")
    #            print(box, boxc,"cards/%d_%d_%d_%d.title.%d.png" % (tile[0], tile[1], tile[2], tile[3], boxc))
    #            print(type(img))
                
                # draw the bounding box on the image
                cv2.rectangle(tshow, (x, y), (x2, y2), (0, 255, 0), 1)

    #            if (not img.empty):
                if (True):
                    cv.imwrite("cards/%d%d.title.%d.png" % (tile[0], tile[1], boxc) , img)

                    tconf = "--oem 3 --psm 7 "+ \
                        "-c tessedit_char_whitelist=\"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-_.\""
                    text = pytesseract.image_to_data(img, config=tconf, output_type='data.frame')
                    text = text[text.conf != -1]
#                    print()
#                    print(text)
                    try:
                        #level,page_num,block_num,par_num,line_num,word_num,left,top,width,height,conf,text        
                        lines = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['text'].apply(lambda x: x.values.tolist()).tolist()
                        confs = text.groupby(['page_num', 'block_num', 'par_num', 'line_num'])['conf'].mean().tolist()
                    
                        tl = []
                        tc = []
                        for i in range(len(lines[0])):
                            if str(lines[0][i]).strip():
                                tl.append(str(lines[0][i]))

                        line = " ".join(tl)  #more likely multiple words, but still can be single word
#                        print(line)

                        conf = 0
                        if (np.any(confs)):
                            conf = round(np.mean(confs),2)
#                        print(conf)

                        words.append(line)
                        tconfs.append(conf)

                    except BaseException as err:
                        print(f"Unexpected {err=}, {type(err)=}")
                        print(tile)
                        print(text)
                        return (tile,None)

            key = "%d%d" % (tile[0], tile[1])

            write = False
#            line = "".join(words)
            mconf = round(np.mean(tconfs),2)
            card = {"key":key, "mconf":mconf, "conf":tconfs, "text":words}
            self.change_text_signal.emit(card)
            
            if key not in self.cardsByTile:
                self.cardsByTile[key] = card
                write = True

            if key in self.cardsByTile:
                if mconf > self.cardsByTile[key]["mconf"]:
                    self.cardsByTile[key] = card
                    write = True
                else:
                    c = self.cardsByTile[key]
                    return(tile,c)

            if write:
                tf = open("cards/%d%d.txt" % (tile[0], tile[1]), "a")
                tf.write(line+"\n")
                tf.write("%.4f\n" % conf)
                tf.close()
                cv.imwrite("cards/%d%d.title.png" % (tile[0], tile[1]) , title)

                return (tile,card)
    #        cv.imwrite("cards/%d_%d_%d_%d.title.png" % (tile[0], tile[1], tile[2], tile[3]) , title)

        return (None,None) 

    def angle_cos(self,p0, p1, p2):
        d1, d2 = (p0-p1).astype('float'), (p2-p1).astype('float')
        return abs( np.dot(d1, d2) / np.sqrt( np.dot(d1, d1)*np.dot(d2, d2) ) )

    def find_squares(self, img):
        thrs2 = 800
        # denoise before edge detection
        blur = cv.GaussianBlur(img,(5,5),0)

        #  normalize color histogram for greater contrast
        #
        clahe = cv.createCLAHE(clipLimit=2.0, tileGridSize=(8,8))
        contrast = clahe.apply(img)

        median_pix = np.median(img)
        if (self.cannyLower is None):
            self.cannyLower = int(max(0 ,0.7*median_pix))
            self.canny_lower_signal.emit(self.cannyLower)

        if (self.cannyUpper is None):
            self.cannyUpper = int(min(255,1.3*median_pix))
            self.canny_upper_signal.emit(self.cannyUpper)

#        print(median_pix, self.cannyLower, self.cannyUpper)

        edge = cv.Canny(contrast, self.cannyLower, self.cannyUpper)#, apertureSize=5)

        # dilate canny output to remove potential
        # holes between edge segments
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (1, 10))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)
        rect_kernel = cv.getStructuringElement(cv.MORPH_RECT, (10, 1))
#               edge = cv.erode(edge, rect_kernel, iterations=1)
        edge = cv.dilate(edge, rect_kernel, iterations=1)

        #im2 = np.uint8(im2/2.)
        #im2[edge != 0] = (0,255,0)
        contours, hierarchy = cv.findContours(edge, 
            cv.RETR_LIST, cv.CHAIN_APPROX_SIMPLE)

        if (self.image_options == "Edge"):
            self.change_pixmap_signal.emit(edge)
        elif (self.image_options == "Edge Contours"):
            im3 = img.copy()
            for i in range(len(contours)):
                cv.drawContours(im3, contours, i, (255, 0, 0), \
                                2, cv.LINE_8, hierarchy, 0)
            self.change_pixmap_signal.emit(im3)

        rect=[]
        for cnt in contours:
            approx = cv.approxPolyDP(cnt,0.02*cv.arcLength(cnt,True),True)
            if (len(approx)==4 and abs(cv.contourArea(cnt)) > (self.tileW * self.tileH)):
                #and abs(cv.contourArea(cnt)) <  ):
#                        print(abs(cv.contourArea(cnt)))
                cnt = approx.reshape(-1, 2)
                max_cos = np.max([self.angle_cos( cnt[i], cnt[(i+1) % 4], cnt[(i+2) % 4] ) for i in range(4)])
                if max_cos < 0.1:
                    rect.append(cnt)
        return rect

    def run(self):
#if 'size' in params:
#    w, h = map(int, params['size'].split('x'))
#vid.set(cv.CAP_PROP_FRAME_WIDTH, 2400)
#vid.set(cv.CAP_PROP_FRAME_HEIGHT, 1080)

        cap = cv.VideoCapture(self.vdev)
        waited=0
        while self._run_flag:
            _ret, orig = cap.read()
            if (orig is None):
                time.sleep(0.1) 
                waited=waited+0.1
                if (waited > self.timeout):
                    cap = cv.VideoCapture(self.vdev)
                    waited=0
                continue
            else:
                self.frame_count += 1

        #    if ((frame_count % 2) != 0):
        #        continue

            #  classically OCR uses white as text foreground and black for background
            #  
            #  MTG typically has black text on a lighter color bg
            #
        #    print('Original Dimensions : ',img.shape)
            self.prev_scale = self.scale_percent
#            scale_percent = cv.getTrackbarPos('scale', 'edge')
            self.width = orig.shape[1]
            self.height = orig.shape[0]
            width = int(orig.shape[1] * self.scale_percent / 100)
            height = int(orig.shape[0] * self.scale_percent / 100)
            dim = (width, height)

            t = self.clock()

            #  split frame into tiles so that we can have an area 
            #  for detected cards to occupy for reference
            #
            ih, iw, ic = orig.shape

            img = cv.resize(orig, dim, interpolation = cv.INTER_AREA)
            im2 = img.copy()

            #  with second plus framerates, show something on program start
            #
            if (self.frame_count == 1 or self.image_options == None or self.image_options == "V4L2"):
                self.change_pixmap_signal.emit(img)

            #try 10 by 10 grid
            rows, cols = 10,10
            tilesize = (int(ih//rows), int(iw//cols))
            self.tilesize = tilesize
            self.tileRows = 10
            self.tileCols = 10
            self.tileW = tilesize[1]
            self.tileH = tilesize[0]
        #    print(ih,iw,tilesize)
        #    print("rows %d, cols %d" % (orig.rows, orig.cols))

            #  first part is card shape detection
            #

        #    fd, hog_image = hog(img, orientations=9, pixels_per_cell=(8, 8),
        #                	cells_per_block=(2, 2), visualize=True, multichannel=True)

        #    cv.imshow('hog', hog_image)

            gray = cv.cvtColor(img, cv.COLOR_BGR2GRAY)

            # denoise before edge detection
            blur = cv.GaussianBlur(gray,(5,5),0)

            if (self.previous_frame is None):
                self.previous_frame = blur
                continue

            if (self.prev_scale != self.scale_percent):
                self.previous_frame = blur
            # motion detection
            #
            # calculate difference and update previous frame
            diff_frame = cv.absdiff(src1=self.previous_frame, src2=blur)
            self.previous_frame = blur

            # 4. Dilute the image a bit to make differences more seeable; more suitable for contour detection
            kernel = np.ones((5, 5))

            #  since this application is supposed to be a still vantage point, we will erode 
            #  to mitigate motion detection as opposed to dilate 
            #
            diff_frame = cv.erode(diff_frame, kernel, 1)

            # 5. Only take different areas that are different enough (>20 / 255)
            thresh_frame = cv.threshold(src=diff_frame, thresh=20, maxval=255, type=cv.THRESH_BINARY)[1]

            #    cv.imshow('dilate', diff_frame)
            #    cv.imshow('motion', thresh_frame)

            #    contours, _ = cv.findContours(image=thresh_frame, mode=cv.RETR_EXTERNAL, method=cv.CHAIN_APPROX_SIMPLE)
            #    imgm = img.copy()
            #    for c in contours:
            #        if cv.contourArea(c) < 50:
            #            continue
            #        (x, y, w, h) = cv.boundingRect(c)
            #        cv.rectangle(img=imgm, pt1=(x, y), pt2=(x + w, y + h), color=(0, 255, 0), thickness=2)
            #        cv.drawContours(thresh_frame, [c], 0, (0, 255, 0), -1)

        #    cv.imshow('motion', thresh_frame)
            if (self.image_options == "Motion"):
                self.change_pixmap_signal.emit(thresh_frame)

        #    cv.drawContours(image=img_rgb, contours=contours, contourIdx=-1, color=(0, 255, 0), thickness=2, lineType=cv2.LINE_AA)

        #    ret, thresh1 = cv.threshold(gray, 175, 255, cv.THRESH_BINARY)


            rect = self.find_squares(blur)

            words = []
            tconfs = []
            if (self.image_options in ["Rects", "Cards"]):
                cardnum=0
                for cnt in rect:
                    cardnum += 1
                    box=cv.boundingRect(cnt)
                    cv.drawContours(im2,[cnt],0,(0,0,255),3)
                    if  (self.image_options == "Cards"):
                        time.sleep(1)
                        self.tap(480,534)
                        time.sleep(1)
                        self.tap(960/2,86/2)

            #  display tile grid
            #
            showts = tuple(int(n * self.scale_percent / 100) for n in tilesize)
            tilecount = 0
            for col in range(cols):
                for row in range(rows):
                    tilecount += 1
                    y0 = row * showts[0]
                    y1 = y0 + showts[0]
                    x0 = col * showts[1]
                    x1 = x0 + showts[1]

                    #show tile grids with tile number text
                    rect = cv.rectangle(im2, (x0, y0), (x1, y1), (127, 127, 127), 1)
                    cv.putText(im2, '%d' % (tilecount),
        #                       (x0 + int(showts[1] / 2), y0 + int(showts[0] / 2)),
                               (x0 + 5, y1 - 20),
                               cv.FONT_HERSHEY_SIMPLEX, 0.5, (127,127,127), 1)

            #  show framerate (time between processed frames)
            #
            dt = self.clock() - t
            cv.putText(im2, 'time: %.1f ms' % (dt*1000), (20, 20), cv.FONT_HERSHEY_SIMPLEX, 0.5, (255,255,255), 2)

#            cv.imshow(method, im2)

            #  escape key
#            if cv.waitKey(5) == 27:
#                break
#            if (self.image_options
            if (self.image_options in ["Rects", "Cards"]):
                self.change_pixmap_signal.emit(im2)
#            print("emitting change_table with:")
#            print(self.cardsByTile)
            self.change_table_signal.emit(self.cardsByTile)

        # shut down capture system
        cap.release()

    def clock(self):
        return cv.getTickCount() / cv.getTickFrequency()

    def get_tile(self,x,y,w,h, tilesize):
        TILE_W = tilesize[1]
        TILE_H = tilesize[0]

        x1 = int(x / TILE_W)
        x2 = (x + w) / TILE_W

        y1 = int(y / TILE_H)
        y2 = (y + h) / TILE_H

        if int(x2) == x2:
            x2 = int(x2 - 1)
        else:
            x2 = int(x2)

        if int(y2) == y2:
            y2 = int(y2 - 1)
        else:
            y2 = int(y2)

        tw = x2 - x1 + 1
        th = y2 - y1 + 1

        return x1+1, y1+1, tw, th

    def stop(self):
        """Sets run flag to False and waits for thread to finish"""
        self._run_flag = False
        self.wait()

    def set_image_options(self, option):
        if (self.debug):
            print("VideoThread: image_options: ", option)
        self.image_options = option

class WorkerSignals(QObject):
    '''
    Defines the signals available from a running worker thread.

    Supported signals are:

    finished
        No data

    error
        tuple (exctype, value, traceback.format_exc() )

    result
        object data returned from processing, anything

    progress
        int indicating % progress

    '''
    finished = pyqtSignal()
    error = pyqtSignal(tuple)
    result = pyqtSignal(object)
    progress = pyqtSignal(int)


class Worker(QRunnable):
    '''
    Worker thread

    Inherits from QRunnable to handler worker thread setup, signals and wrap-up.

    :param callback: The function callback to run on this worker thread. Supplied args and
                     kwargs will be passed through to the runner.
    :type callback: function
    :param args: Arguments to pass to the callback function
    :param kwargs: Keywords to pass to the callback function

    '''

    def __init__(self, uri, args, key):
        super(Worker, self).__init__()

        # Store constructor arguments (re-used for processing)
        self.fn = self.request
        self.uri = uri
        self.args = args
        self.key = key
        self.signals = WorkerSignals()

    def request(self):
        print("sending request to %s with %s" % (self.uri, self.args))
        response = requests.get(self.uri+self.args)
        json_response = json.loads(response.text)
        json_response["request"] = {"uri":self.uri, "args":self.args, "key":self.key}
        return json_response

    def print_output(self):
        print(self.response)

    @pyqtSlot()
    def run(self):
        '''
        Initialise the runner function with passed args, kwargs.

        # Retrieve args/kwargs here; and fire processing using them
        '''
        try:
            result = self.request()
        except:
            traceback.print_exc()
            exctype, value = sys.exc_info()[:2]
            self.signals.error.emit((exctype, value, traceback.format_exc()))
        else:
            self.signals.result.emit(result)  # Return the result of the processing
        finally:
            self.signals.finished.emit()  # Done

class RequestPool(QObject):
    on_request_result = pyqtSignal(object)
    def __init__(self):
        super().__init__()
        self.threadpool = QThreadPool()

        self.timer = QTimer()
        self.timer.setInterval(1000)
        self.timer.timeout.connect(self.recurring_timer)
        self.timer.start()
        self.uri = "https://api.scryfall.com/cards/named?fuzzy="
        self.counter = 0


    def recurring_timer(self):
        self.counter +=1

        # Execute
#        self.threadpool.start(worker)

    def result(self, response):
        (key, args, name, image, price, link) = (None, None, None, None, None,None)
        print("request pool result for %s: " % response["request"]["args"])

        args = response["request"]["args"]
        key = response["request"]["key"]

#        {'object': 'error', 'code': 'not_found', 'status': 404, 'details': 'No cards found matching “ein Eldest Redorn”'}
        try:
            print(" name  : %s" % response["name"])
            name = response["name"]
        except:
            print(response)
            return

        try:
            print(" image : %s" % response["image_uris"]["small"])
            image = response["image_uris"]["small"]
        except:
            pass

        try:
            print(" price : %s" % response["prices"]["usd"])
            price = response["prices"]["usd"]
        except:
            pass
  
        try:
            link = response["related_uris"]["gatherer"]
        except:
            pass
  
        card = {"key":key, "args":args, "name": name, "image":image, "price":price, "link": link}
        print("emit on_request_result signal ", card)
        self.on_request_result.emit(card)

        

    def make_request(self,arg,key):
        print(f"RequestPool make_request:{arg}")
        # Pass the function to execute
        uri = self.uri + arg
        worker = Worker(self.uri,arg,key) # Any other args, kwargs are passed to the run function
#        worker.signals.finished.connect(self.thread_complete)
#        worker.signals.progress.connect(self.progress_fn)
        worker.signals.result.connect(self.result)
        # Execute
        self.threadpool.start(worker)


class CardDetails(QWidget):
    def __init__(self):
        super().__init__()

        vbox = QVBoxLayout()
        #  card number as on grid, text, confidence, price
        self.table = QTableWidget(2,4)
        vbox.addWidget(self.table)
        self.setLayout(vbox)


#        self.l.setText("Counter: %d" % self.counter)
    @pyqtSlot(dict)
    def request_result(self, card):
        print("Card Detail:request_result:", card)
        column = 0
        # rowCount() This property holds the number of rows in the table
        for row in range(self.table.rowCount()): 
            # item(row, 0) Returns the item for the given row and column if one has been set; otherwise returns nullptr.
            _item = self.table.item(row, column) 
            if _item:            
                key = self.table.item(row, column).text()
                if (key == card["key"]):
                    self.table.setItem(row,3, QTableWidgetItem(card['name']))
                    self.table.setItem(row,4, QTableWidgetItem(card['price']))
                    self.table.setItem(row,5, QTableWidgetItem(card['image']))
                    self.table.setItem(row,6, QTableWidgetItem(card['link']))

    @pyqtSlot(dict)
    def update_table(self, cardsByTile):
#        print("update table, recieved :")
#        print(cardsByTile)
        #Row count
        self.table.setRowCount(len(cardsByTile))
  
        #Column count
        self.table.setColumnCount(7)
        self.table.setSortingEnabled(False) 
        self.table.setHorizontalHeaderLabels(['Tile', 'Text', 'Confidence', 'Name', 'Price', 'Image', 'Link'])
        self.table.setShowGrid(False)
        self.table.setAlternatingRowColors(True)

        for n, tile in enumerate(sorted(cardsByTile.keys())):
            card = cardsByTile[tile]
            prev = self.table.item(n,0)
            if (prev is not None):
                name = self.table.item(n, 3)
                if (name is not None):
                    continue
            self.table.setItem(n,0, QTableWidgetItem(tile))
            self.table.setItem(n,1, QTableWidgetItem(" ".join(card["text"])))
            self.table.setItem(n,2, QTableWidgetItem("%.2f" % card["mconf"]))

        #Table will fit the screen horizontally
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.horizontalHeader().setSectionResizeMode(
            QHeaderView.Stretch)

        self.table.resizeColumnsToContents()
        self.table.resizeRowsToContents()
        self.table.setEditTriggers(QTableWidget.NoEditTriggers)
        self.table.show()

class TransparentOverlay(QWidget):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.setAttribute(QtCore.Qt.WA_NoSystemBackground)
        self._updateParent(self.parentWidget())

    def setParent(self, parent, *args):
        prevParent = self.parentWidget()
        super().setParent(parent, *args)
        self._updateParent(parent, prevParent)

    def unsetParent(self, parent=None):
        if parent is None:
            parent = self.parentWidget()
        if parent is not None and hasattr(parent.resizeEvent, '_original'):
            parent.resizeEvent = parent.resizeEvent._original

    def _updateParent(self, parent, prevParent=None):
        if parent is not prevParent:
            self.unsetParent(prevParent)
            if parent is not None:
                original = parent.resizeEvent
                def resizeEventWrapper(event):
                    original(event)
                    self.resize(event.size())
                resizeEventWrapper._original = original
                parent.resizeEvent = resizeEventWrapper
                self.resize(parent.size())

proc = None
class ImageControl(QWidget):
    check_option_signal = pyqtSignal(str)

    def imageOptionClicked(self, state):
        isChecked = bool(state)
        if (isChecked):
            cb = self.checkBoxes.checkedButton()
            if (cb):
                if (self.debug):
                    print("imageOptionClicked: ",cb.text())
                self.check_option_signal.emit(cb.text())
            else:
                print("unknown button checked")

    def setCannyLower(self):
        self.thread.cannyLower = self.t1Slider.value()

    def updateCannyLower(self, value):
        self.t1Slider.setValue(value)

    def setCannyUpper(self):
        self.thread.cannyUpper = self.t2Slider.value()

    def updateCannyUpper(self,value):
        self.t2Slider.setValue(value)

    def setSliderLabels(self):
        self.t1Label.setText("%d" % self.t1Slider.value())
        self.t2Label.setText("%d" % self.t2Slider.value())

    def _on_resized(self, event):
        '''
        print(ppretty(event, indent='    ', depth=2, width=30, seq_length=6,
              show_protected=True, show_private=False, show_static=True,
              show_properties=True, show_address=True))
        '''
        ow = event.oldSize().width()
        oh = event.oldSize().height()

        w = event.size().width()
        h = event.size().height()

        wd = w - ow
        hd = h - oh

        print(event.oldSize(), event.size())
        print((ow,oh), (w, h), (wd, hd))

#        self.display_width += wd
#        self.display_height += hd

#        self.image_label.resize(self.display_width, self.display_height)

    def __init__(self):
        super().__init__()
        self.requestPool = RequestPool()

        self.resizeEvent = (lambda old_method: (lambda event: (self._on_resized(event), old_method(event))[-1]))(self.resizeEvent)
        #serial = "FAMVRW9D9HDEHEWS" #BLU Pure
#        self.serial="XG9LGEZX6L75QGMJ" #Oppo Realme RMX2001
        self.serial="0123456789ABCDEF"
        try:
            self.serial = os.environ['ANDROID_SERIAL']
        except:
            pass

        parser = optparse.OptionParser()
        parser.set_defaults(debug=False)
        parser.add_option('-d', '--debug', action='store_true', dest='debug')
        parser.add_option('--device', type="int", dest='device',
                         help="video device # to read from", default="0")
        parser.add_option('-l', '--lower', type="int", dest='lower', \
                            help="lower canny threshold for rectangle detection processing")
        parser.add_option('-u', '--upper', type="int", dest='upper', \
                            help="upper canny threshold")
        (o, args) = parser.parse_args()

        self.debug = False
        if o.debug:
            self.debug = bool(options.debug)

        self.vdev = 0
        if o.device:
            self.vdev = int(o.device)

        self.cannyLower = None
        if o.lower:
            self.cannyLower = int(o.lower)

        self.cannyUpper = None
        if o.upper:
            self.cannyUpper = int(o.upper)

        self.setWindowTitle("Image Processing Control")
        self.timeout=5
        self.display_width = 1080
        self.display_height = 960
        # create the label that holds the image
        self.image_label = QLabel(self)
        self.image_label.resize(self.display_width, self.display_height)

        # create a text label
        self.textLabel = QLabel('/dev/video%d' % self.vdev)
        self.snapBtn = QPushButton('Snapshot')
        self.takeSnapshot = False
        self.snapBtn.clicked.connect(self.snapshot)

        self.t1Slider = QSlider(Qt.Horizontal)
        self.t2Slider = QSlider(Qt.Horizontal)
        self.t1Slider.setMinimum(0)
        self.t2Slider.setMinimum(0)
        self.t1Slider.setMaximum(255)
        self.t2Slider.setMaximum(255)
        try:
            self.t1Slider.setValue(self.cannyLower)
        except:
            self.t1Slider.setValue(0)

        try:
            self.t2Slider.setValue(self.cannyUpper)
        except:
            self.t2Slider.setValue(255)

        self.t1Label = QLabel("%d" % self.t1Slider.value())
        self.t2Label = QLabel("%d" % self.t2Slider.value())
        self.t1Slider.setTickPosition(QSlider.TicksBelow)
        self.t2Slider.setTickPosition(QSlider.TicksBelow)
        self.t1Slider.setTickInterval(5)
        self.t2Slider.setTickInterval(5)
        self.t1Slider.valueChanged.connect(self.setSliderLabels)
        self.t2Slider.valueChanged.connect(self.setSliderLabels)
        self.t1Slider.sliderReleased.connect(self.setCannyLower)
        self.t2Slider.sliderReleased.connect(self.setCannyUpper)


        self.checkBoxes = QButtonGroup()
        #'image options')

        hbox = QHBoxLayout()
        hbox.addWidget(self.snapBtn)
        options = [QCheckBox("V4L2"), QCheckBox("Rects"), QCheckBox("Cards"), QCheckBox("Edge"), QCheckBox("Edge Contours"), QCheckBox("Motion")]
        options[0].setChecked(True)
        for i in range(len(options)):
            hbox.addWidget(options[i])
            self.checkBoxes.addButton(options[i], i)
            options[i].stateChanged.connect(self.imageOptionClicked)

        vbox = QVBoxLayout()
        vbox.addWidget(self.image_label)
        vbox.addLayout(hbox)
        hbt1 = QHBoxLayout()
        hbt2 = QHBoxLayout()
        hbt1.addWidget(self.t1Label)
        hbt1.addWidget(self.t1Slider)
        hbt2.addWidget(self.t2Label)
        hbt2.addWidget(self.t2Slider)
        vbox.addLayout(hbt1)
        vbox.addLayout(hbt2)
        vbox.addWidget(self.t2Slider)
        vbox.addWidget(self.textLabel)
        
        # set the vbox layout as the widgets layout
        self.setLayout(vbox)

        print("capture /dev/video%d\n" % self.vdev)

    @pyqtSlot(dict)
    def validate_text(self, card):

        #camecase, join with space
        phrase = ""
        for word in card["text"]:
            if (word.istitle()):
                phrase = "+".join([phrase, urllib.parse.quote(word)])
            else:
                phrase = "".join([phrase, urllib.parse.quote(word)])

        #even though this is likely the correct construction of the phrase,
        # there is a chance tesseract had a better OCR on one word over the other

        print("validate_text: make_request phrase %s -> %s" % ("".join(card["text"]), phrase))
        if (float(card["mconf"]) > -1):
            print(card['mconf'])
            self.requestPool.make_request(phrase, card["key"])
        else:
            print(card['mconf'])


    def run(self):
        #  will block for either timeout or time until success string outputs
        #  proc used in handler
        (proc, q) = self.v4l2sink()

        self.isRunningOrStart() #open camera on android device

        self.table = CardDetails()
        self.table.show()

        # create the video capture thread
        self.thread = VideoThread(vdev=self.vdev,lower=self.cannyLower,upper=self.cannyUpper, debug=self.debug)
        # connect its signal to the update_image slot
        self.thread.change_pixmap_signal.connect(self.update_image)
        self.check_option_signal.connect(self.thread.set_image_options)
        self.thread.canny_lower_signal.connect(self.updateCannyLower)
        self.thread.canny_upper_signal.connect(self.updateCannyUpper)

        self.thread.change_table_signal.connect(self.table.update_table)
        self.requestPool.on_request_result.connect(self.table.request_result)
        self.thread.change_text_signal.connect(self.validate_text)

        #  wait for signals to be detected so initial state is set
        #
        # start the thread
        self.thread.start()


    #  check for existing scrcpy using v42l-sink
    #  if non, start one
    #    TODO: handle errors from scrcpy
    #
    def v4l2sink(self,devN=0):

        #  check for process being run externally
        #
        try:
            fuser = subprocess.run(['fuser', "/dev/video%d" % devN], check=True, capture_output=True, text=True)
            if (len(fuser.stdout) > 0):
                m = re.match(r".*?:?\s*(?P<pid>\d+).*", fuser.stdout)
                ps = subprocess.run(['ps','-q', str(m.group('pid')), '-o', 'user=,pid=,state=,tname=,time=,command='], check=True, capture_output=True, text=True)
                if (len(ps.stdout) > 0):
                    print("v4l2 device video%d in use by the following:\n" % devN, ps.stdout)
                    return (False,False)
        except subprocess.CalledProcessError as e:
            if (e.returncode == 1 and len(e.output) == 0):
                print("v4l2 device has no current user")
            else:
                print(e.returncode)
                print(e.output)
        except BaseException as err:
            previous_frame = inspect.currentframe().f_back
            (filename, line_number, function_name, lines, index) = inspect.getframeinfo(previous_frame)
            print(f"Unexpected {err=}, {type(err)=}", line_number, lines)
            pass

        #  begin v4l2_sink with scrcpy as Popen thread with threaded output readers
        #
        print("v4l2 device currently free, starting scrcpy")
    #    cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % serial
#        cmd = "scrcpy -s %s --lock-video-orientation=3 --v4l2-sink=/dev/video0 --stay-awake --power-off-on-close --no-display --show-touches" % self.serial
        cmd = "scrcpy -s %s -m960 --v4l2-sink=/dev/video0 --stay-awake --no-display --show-touches" % self.serial
        print(cmd)
        proc = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        pq = queue.Queue()
        t1 = threading.Thread(target=stdout_reader, args=(proc, pq))
        t1.start()
        t2 = threading.Thread(target=stderr_reader, args=(proc, pq))
        t2.start()

        wait = isinstance(proc, subprocess.Popen)
        waited = 0
        self.timeout = 5
        while wait and waited < self.timeout:
            try:
                line = pq.get(block=False)

                if (re.match(r"(WARN|INFO|ERROR|\[server).*", line)):
                    print('{0}'.format(line), end='')
            #INFO: v4l2 sink started to device: /dev/video0
                m = re.match(r".*?v4l2 sink started to device: (?P<device>[\/\w]+)", line)
        #        m = re.match(r".*?v4l2 sink started to device: ", line)
                if (m):
                    print("scrcpy v4l2 sink started using device %s" % m.group('device'))
                    wait = False
                #
                #  TODO what are the error strings from scrcpy or v4l2?
                #
            except queue.Empty:
                pass
            time.sleep(0.01) 
            waited += 0.01

        return (proc, pq)

    def checkCurrentFocus(self):
        cmd = "adb -s %s shell dumpsys window windows | grep -E 'mCurrentFocus|mFocusedApp|mHoldScreenWindow'"
        result = subprocess.run(cmd.split(), capture_output=True, text=True)
        return result.stdout

    #  for future reference,
    #   setting up open camera
    #  video mode, hide all gui elements
    #  set resolution to that of phone screen size
    #  enable digital video stabilization
    #  preference_auto_stabilise = true (auto level in gui)
    #    images mat be smaller resolution due to rotating and cropping
    #
    def isRunningOrStart(self,package="net.sourceforge.opencamera"):
        focus=self.checkCurrentFocus()
        m = re.match(r".*?%s.*" % package,focus)
        if (m):
            return
        else:
            cmd = "adb -s %s shell monkey -p %s -c android.intent.category.LAUNCHER 1" % (self.serial,package)
            result = subprocess.run(cmd.split(), capture_output=True, text=True)



    def closeEvent(self, event):
        self.table.close()
        self.thread.stop()
        event.accept()

    @pyqtSlot(np.ndarray)
    def update_image(self, cv_img):
        """Updates the image_label with a new opencv image"""
        qt_img = self.convert_cv_qt(cv_img)
        self.image_label.setPixmap(qt_img)
    
    def snapshot(self):
        self.takeSnapshot = True

    def convert_cv_qt(self, cv_img):
        if (self.takeSnapshot == True):
            self.takeSnapshot = False
            cv.imwrite("snapshot.png", cv_img)
        """Convert from an opencv image to QPixmap"""
        rgb_image = cv.cvtColor(cv_img, cv2.COLOR_BGR2RGB)
        h, w, ch = rgb_image.shape
        bytes_per_line = ch * w
        convert_to_Qt_format = QtGui.QImage(rgb_image.data, w, h, bytes_per_line, QtGui.QImage.Format_RGB888)
        p = convert_to_Qt_format.scaled(self.display_width, self.display_height, Qt.KeepAspectRatio)
        return QPixmap.fromImage(p)
    
if __name__=="__main__":
    signal.signal(signal.SIGINT, handler)
    app = QApplication(sys.argv)
    main = ImageControl()
    main.run()
    cb = main.checkBoxes.checkedButton()
    if (cb):
        print("imageOptionClicked: ",cb.text())
        main.check_option_signal.emit(cb.text())
    main.show()
    #  cleanup after Popen
    frame = inspect.currentframe()
    handler(signal.SIGINT, frame)


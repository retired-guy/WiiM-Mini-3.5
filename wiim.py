#!/usr/bin/python3
# -*- coding: utf-8 -*-
# pylint: disable=invalid-name

from time import sleep
import requests
import textwrap
import re

import asyncio
import json
import logging
import operator
import sys
import time
import xmltodict
from datetime import datetime
from typing import Any, Optional, Sequence, Tuple, Union, cast
from collections import OrderedDict

from didl_lite import didl_lite
NAMESPACES = {
    "didl_lite": "urn:schemas-upnp-org:metadata-1-0/DIDL-Lite/",
    "dc": "http://purl.org/dc/elements/1.1/",
    "upnp": "urn:schemas-upnp-org:metadata-1-0/upnp/",
    "xsi": "http://www.w3.org/2001/XMLSchema-instance",
    "song": "www.wiimu.com/song/",
    "custom": "www.linkplay.com/custom/",
}

from async_upnp_client.advertisement import SsdpAdvertisementListener
from async_upnp_client.aiohttp import AiohttpNotifyServer, AiohttpRequester
from async_upnp_client.client import UpnpDevice, UpnpService, UpnpStateVariable
from async_upnp_client.client_factory import UpnpFactory
from async_upnp_client.const import NS, AddressTupleVXType, SsdpHeaders
from async_upnp_client.exceptions import UpnpResponseError
from async_upnp_client.profiles.dlna import dlna_handle_notify_last_change
from async_upnp_client.search import async_search as async_ssdp_search
from async_upnp_client.ssdp import SSDP_IP_V4, SSDP_IP_V6, SSDP_PORT, SSDP_ST_ALL
from async_upnp_client.utils import get_local_ip

from PIL import Image
from PIL import ImageFont
from PIL import ImageDraw

###### I/O devices may be different on your setup #####
###### can optionally use numpy to write to fb ########
#h, w, c = 320, 480, 4
#fb = np.memmap('/dev/fb0', dtype='uint8',mode='w+',shape=(h,w,c))

fbw, fbh = 480, 320         # framebuffer dimensions
fb = open("/dev/fb0", "wb") # framebuffer device

#######################################################

fonts = []
fonts.append( ImageFont.truetype('/usr/share/fonts/truetype/oswald/Oswald-Bold.ttf', 24) )
fonts.append( ImageFont.truetype('/usr/share/fonts/truetype/oswald/Oswald-Light.ttf', 20) )
fonts.append( ImageFont.truetype('/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf', 30) )
fonts.append( ImageFont.truetype('/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf', 144) )

## Red and Blue color channels are reversed from normal RGB on pi framebuffer
def swap_redblue(img):
  "Swap red and blue channels in image"
  r, g, b, a = img.split()
  return Image.merge("RGBA", (b, g, r, a))

## Paint image to screen at position
def blit(img, pos):

  size = img.size
  w = size[0]
  h = size[1]
  x = pos[0]
  y = pos[1]

### to use numpy, uncomment...
#  n = np.array(img)
#  n[:,:,[0,1,2]] = n[:,:,[2,1,0]]
#  fb[y:y+h,x:x+w] = n
### ... and comment all below

  img = swap_redblue(img)
  try:
    fb.seek(4 * ((pos[1]) * fbw + pos[0]))
  except Exception as e:
    print("seek error: ", e)

  iby = img.tobytes()
  for i in range(h):
    try:
      fb.write(iby[4*i*w:4*(i+1)*w])
      fb.seek(4 * (fbw - w), 1)
    except Exception as e:
      break


## Display date and time when idle
def displaydatetime(force):

  if not force:
    sec = datetime.now().second
    if sec not in {0,15,30,45}:
      return 

  dt = datetime.today().strftime('%a, %d %B %Y')
  tm = datetime.today().strftime('%H:%M')

  img = Image.new('RGBA',(480, 320))
  draw = ImageDraw.Draw(img)
  
  draw.text((20,10), tm, (255,255,255),font=fonts[3])
  draw.text((65,200), dt, (255,255,255),font=fonts[2])

  blit(img,(0,0))


## Red song progress line
def displayprogress(seek, duration):

  if duration > 0:
    progress = seek / duration * 480
  else:
    progress = 0

  img = Image.new('RGBA', (480, 6))

  draw = ImageDraw.Draw(img)
  draw.line((0,0,progress,0),fill='red',width=6)

  blit(img,(0,44))

def clearscreen():
   img = Image.new('RGBA',size=(480,320),color=(0,0,0,255))
   blit(img,(0,0))

## Display artist, song title, album title
def displaymeta(data):

  img = Image.new('RGBA',size=(210,270),color=(0,0,0,255))

  tw1 = textwrap.TextWrapper(width=30)
  tw2 = textwrap.TextWrapper(width=30)
  s = "\n"

  try:
    artist = data['upnp:artist']
  except:
    artist = ""

  try:
    title = data['dc:title']
  except:
    title = ""

  try:
    album = data['upnp:album']
  except:
    album = ""

  if album == "":
    try:
      album = data['dc:subtitle']
    except:
      pass

  artist = s.join(tw2.wrap(artist)[:6])
  album = s.join(tw2.wrap(album)[:6])

  draw = ImageDraw.Draw(img)

  draw.text((10,0), artist, (191,245,245),font=fonts[1])
  draw.text((10,165), album, (255,255,255),font=fonts[1])

  blit(img,(270,50))

  img = Image.new('RGBA',size=(480,50),color=(0,0,0,255))
  draw = ImageDraw.Draw(img)
  draw.text((0,0),  title, (255,255,255),font=fonts[0])

  blit(img,(0,0))

## Get album cover and display
def getcoverart(url):

  try:
    img = Image.open(requests.get(url, stream=True).raw)
    img = img.resize((270,270))
    img = img.convert('RGBA')

    blit(img,(0,50))
  except Exception as e:
    print(e)
    pass

## Init the screen
displaydatetime(True)

detail = [] 
items = {} 
art = ""

pprint_indent = 4

event_handler = None
playing = False

async def create_device(description_url: str) -> UpnpDevice:
    """Create UpnpDevice."""
    timeout = 60
    non_strict = True
    requester = AiohttpRequester(timeout)
    factory = UpnpFactory(requester, non_strict=non_strict)
    return await factory.async_create_device(description_url)


def get_timestamp() -> Union[str, float]:
    """Timestamp depending on configuration."""
    return time.time()


def service_from_device(device: UpnpDevice, service_name: str) -> Optional[UpnpService]:
    """Get UpnpService from UpnpDevice by name or part or abbreviation."""
    for service in device.all_services:
        part = service.service_id.split(":")[-1]
        abbr = "".join([c for c in part if c.isupper()])
        if service_name in (service.service_type, part, abbr):
            return service

    return None

def on_event(
    service: UpnpService, service_variables: Sequence[UpnpStateVariable]
) -> None:
    """Handle a UPnP event."""
    obj = {
        "timestamp": get_timestamp(),
        "service_id": service.service_id,
        "service_type": service.service_type,
        "state_variables": {sv.name: sv.value for sv in service_variables},
    }
    global playing
    global items
    global art 
    
    # special handling for DLNA LastChange state variable
    if len(service_variables) == 1 and service_variables[0].name == "LastChange":
        last_change = service_variables[0]
        dlna_handle_notify_last_change(last_change)
    else:
        for sv in service_variables:
            ### PAUSED, PLAYING, STOPPED, etc
            #print(sv.name,sv.value)
            if sv.name == "TransportState":
                print(sv.value)
                if sv.value == "PLAYING":
                  playing = True
                  displaymeta(items)
                  if art:
                    getcoverart(art)
                else:
                  playing = False

            ### Grab and print the metadata
            if sv.name == "CurrentTrackMetaData" or sv.name == "AVTransportURIMetaData":
                ### Convert the grubby XML to beautiful JSON, because we HATE XML!
                items = xmltodict.parse(sv.value)["DIDL-Lite"]["item"]
                ### Print the entire mess
                print(json.dumps(items,indent=4))

                ### Print each item of interest
                try:
                  title = items["dc:title"]
                  print("Title:",title)
                  displaymeta(items)
                except:
                  pass

                try:
                  subtitle = items["dc:subtitle"]
                  print("Subtitle:",subtitle)
                except:
                  pass

                try:
                  artist = items["upnp:artist"]
                  print("Artist:",artist)
                except:
                  pass

                try:
                  album = items["upnp:album"]
                  print("Album:",album)
                except:
                  pass

                try:
                  arttmp = items["upnp:albumArtURI"]
                  if isinstance(arttmp, dict):
                    art = art["#text"]
                  else:
                    art = arttmp

                  print("Art:",art)
                  getcoverart(art)
                except:
                  pass


async def subscribe(description_url: str, service_names: Any) -> None:
    """Subscribe to service(s) and output updates."""
    global event_handler  # pylint: disable=global-statement

    device = await create_device(description_url)

    # start notify server/event handler
    source = (get_local_ip(device.device_url), 0)
    server = AiohttpNotifyServer(device.requester, source=source)
    await server.async_start_server()

    # gather all wanted services
    if "*" in service_names:
        service_names = device.services.keys()

    services = []

    for service_name in service_names:
        service = service_from_device(device, service_name)
        if not service:
            print(f"Unknown service: {service_name}")
            sys.exit(1)
        service.on_event = on_event
        services.append(service)

    # subscribe to services
    event_handler = server.event_handler
    for service in services:
       try:
            await event_handler.async_subscribe(service)
       except UpnpResponseError as ex:
            print("Unable to subscribe to %s: %s", service, ex)

    s = 0
    # keep the webservice running
    while True:
        if playing == False:
          displaydatetime(True)

        await asyncio.sleep(10)
        s = s + 1
        if s >= 12:
          await event_handler.async_resubscribe_all()
          s = 0

async def async_main() -> None:
    """Async main."""

    ####  NOTICE!!!! #####################################
    ####  Your WiiM Mini's IP and port go here
    device = "http://192.168.68.112:49152/description.xml"
    ####             #####################################
    service = ["AVTransport"]

    await subscribe(device, service)


def main() -> None:
    """Set up async loop and run the main program."""
    loop = asyncio.get_event_loop()

    try:
        loop.run_until_complete(async_main())
    except KeyboardInterrupt:
        if event_handler:
            loop.run_until_complete(event_handler.async_unsubscribe_all())
    finally:
        loop.close()


if __name__ == "__main__":
    main()


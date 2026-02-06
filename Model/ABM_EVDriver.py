from __future__ import annotations

import mesa
from mesa.space import NetworkGrid
import pandas as pd
from mesa.datacollection import DataCollector
from __future__ import annotations
from collections import OrderedDict
from typing import Dict, Iterator, List, Optional, Union
from mesa import Model
from mesa import Agent
from typing import Dict, Iterator, List, Optional, Union
from geopandas import GeoDataFrame, sjoin
import osmnx as ox
import networkx as nx
import numpy as np
import geopandas as gpd
import matplotlib
import matplotlib.pyplot as plt
import igraph
import random
import folium
import operator
import geopy
from geopy import distance
import SALib
from SALib.sample import saltelli
from SALib.analyze import sobol
from tqdm import tqdm
import csv
from statistics import mean
from scipy.spatial import cKDTree
import json
import igraph as ig
import random
import pickle

EV_agent = pd.read_json(r'/home/ec2-user/ABM_model/data/ev_data_full_1.json', orient='records', lines=True)

with open(r'/home/ec2-user/ABM_model/data/station_avail_1day.json', 'r') as file:
    station_avail = json.load(file)

with open(r'/home/ec2-user/ABM_model/data/station_location.json', 'r') as file:
    station_location = json.load(file)

with open(r'/home/ec2-user/ABM_model/data/station_info_incl_park.json', 'r') as file:
    station_info = json.load(file)

with open(r'/home/ec2-user/ABM_model/data/id_mapping.json', 'r') as file:
    id_mapping = json.load(file)

with open(r'/home/ec2-user/ABM_model/data/edge_lengths.json', 'r') as file:
    edge_lengths = json.load(file)

with open(r'/home/ec2-user/ABM_model/data/station_node.json', 'r') as file:
    station_node = json.load(file)

g = ig.load(r'/home/ec2-user/ABM_model/data/GB_network_relabeled_H1.graphml')
networkx_graph = ig.Graph.to_networkx(g)

class EV(Agent):
    def __init__ (self,
                  unique_id : int,
                  full_battery: float,
                  consum_rate: float, # need to be KWh/m,
                  soc_threshold: float, #be a percentage
                  #speed_list:list, #meter/minute (a list)
                  trip_plan:list, # key as trip_id, value as a list [origin, destination, start_time], len(trip_plan)>1 if multiple trips in a day
                  alpha,
                  beta,
                  model: EV_Model):
        super().__init__(unique_id, model)


        self.trip_idx = 0
        self.trip_plan = trip_plan
        self.agent_type = 'EV'
        self.full_battery = full_battery
        self.consum_rate = consum_rate
        self.soc_threshold = soc_threshold
        self.alpha = alpha
        self.beta = beta
        self.init_node = None
        self.init_soc_random = random.random()
        self.battery = self.full_battery *self.init_soc_random
        # evaluation
        self.status_idx = []
        self.battery_idx =[]
        self.route_idx = []
        self.ev_time_idx = []
        self.trip_left = len(self.trip_plan)
        self.current_trip = None
        self.status = 'stay'
        self.orig = 0
        self.dest = 0
        self.ev_time = 0
        self.current_pos = 0
        self.target_pos = 0
        self.shortest_path = None
        self.shortest_path_length = 0
        self.speed = None

        self.trip_start_time = 0
        self.charge_need_to_dest = 0
        #drive to destination
        self.travelled_dis = 0
        #ask for stations
        self.pos_lat = 0
        self.pos_lon = 0
        self.current_coor = None
        self.candidate_stations =[]
        #choose dwell station
        self.candidate_stations_info ={}
        self.candidate_station_speed_list = []
        self.stay_time= 0
        self.charge_amount_list = []
        self.chosen_amount_station = None
        self.chosen_charge_amount = 0
        self.chosen_station = None
        self.chosen_price = 0
        self.chosen_speed = 0
        self.charge_time_length = 0
        self.expect_charge_end_time= 0
        #charge plan
        self.capable_distance = 0
        self.desperate_number = 0
        self.candidate_distance_dict =[]
        #drive to selected station
        self.shortest_path_to_station = None
        self.shortest_path_length_to_station = 0
        # charge en route
        self.charge_start_time = 0
        self.charge_end_time = 0
        # consider reselect station
        self.needed_amount = 0
        #queue
        self.queue_choices = []
        self.queue_choice = None
        self.current_trip_id = None
        self.diary = []

        #self.alpha = random.gauss(0.5, 0.167) # range 0-1
        #self.beta = 1-self.alpha
        #self.soc_threshold = random.gauss(0.5, 0.167) # range 0-1
        #self.consum_rate = random.gauss(0.0002, 0.0000167) # range 0.00015, 0.00025


        self.distance_idx = []
        self.distance_cost_value = 0
        self.time_cost_value =0
        self.finance_cost_value = 0
        self.payment = 0
        self.finance_idx = []
        self.time_charge_idx = []
        self.total_cost = 0

        self.total_cost_idx = []
        self.total_finance_idx = []
        self.total_time_idx =[]
        self.distance_cost_idx = []
        self.used_station =[]
        self.charge_time_record_idx = []

        self.charge_time_record = 0

    def initialisation (self):
            self.trip_left = len(self.trip_plan)
      self.trip_idx  = 0
      self.init_node = None
      self.current_trip = None
      self.status = 'stay'
      self.orig = 0
      self.dest = 0
      self.ev_time = 0
      self.current_pos = 0
      self.target_pos = 0
      self.shortest_path = None
      self.shortest_path_length = 0
      self.trip_start_time = 0
      self.charge_need_to_dest = 0
      self.travelled_dis = 0
      self.pos_lat = 0
      self.pos_lon = 0
      self.current_coor = None
      self.candidate_stations =[]
      self.candidate_stations_info ={}
      self.candidate_station_speed_list = []
      self.stay_time= 0
      self.charge_amount_list = []
      self.chosen_amount_station = None
      self.chosen_charge_amount = 0
      self.chosen_station = None
      self.chosen_price = 0
      self.chosen_speed = 0
      self.charge_time_length = 0
      self.expect_charge_end_time= 0
      self.capable_distance = 0
      self.desperate_number = 0
      self.candidate_distance_dict =[]
      self.shortest_path_to_station = None
      self.shortest_path_length_to_station = 0
      self.charge_start_time = 0
      self.charge_end_time = 0
      self.needed_amount = 0
      self.queue_choices = []
      self.queue_choice = None
      self.current_trip_id = None

      self.distance_idx = []
      self.distance_cost_value = 0
      self.time_cost_value =0
      self.finance_cost_value = 0
      self.payment = 0
      self.finance_idx = []
      self.time_charge_idx = []
      self.total_cost = 0
      self.charge_time_value_record = 0

    def evaluation (self):
        self.diary.append('evaluation')
        self.status_idx.append('start')
        self.current_trip_id = list(self.trip_plan[self.trip_idx].keys())[0]
        self.current_trip = self.trip_plan[self.trip_idx]
        self.orig = list(self.trip_plan[self.trip_idx].values())[0][0]
        self.dest = list(self.trip_plan[self.trip_idx].values())[0][1]
        self.trip_start_time = list(self.trip_plan[self.trip_idx].values())[0][2]
        self.speed  = list(self.trip_plan[self.trip_idx].values())[0][3]

        self.current_pos = self.orig
        self.target_pos = self.dest
        self.ev_time = self.trip_start_time

        self.shortest_path = g.get_shortest_path(v = self.orig, to = self.dest, weights = g.es['length'], output = 'vpath')
        self.shortest_path_length = (g.distances(source = self.orig, target = self.dest, weights = 'length'))[0][0]
        self.charge_need_to_dest = self.consum_rate*self.shortest_path_length

        if self.battery >=  self.charge_need_to_dest:
            self.drive_to_destination()
        else:
            self.charge_plan()

    def drive_to_destination (self):

        self.diary.append('drive_to_destination')
        self.status_idx.append(self.status)
        self.route_idx.append(self.current_pos)
        self.battery_idx.append(self.battery)
        self.ev_time_idx.append(self.ev_time)
        self.status = 'drive'

        i = 1
        while i < len(self.shortest_path):
            self.model.grid.move_agent(self,self.shortest_path[i])
            self.current_pos = self.shortest_path[i]
            edge = g.get_eid(self.shortest_path[i - 1], self.shortest_path[i])
            self.travelled_dis = g.es[edge]['length']
            self.distance_idx.append(self.travelled_dis)
            #edge = ((self.shortest_path[i - 1]), self.shortest_path[i])
            #self.travelled_dis = edge_lengths[str(edge)]
            self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
            self.ev_time = self.travelled_dis/self.speed + self.ev_time
            self.battery = self.battery - self.travelled_dis*self.consum_rate
            self.battery_idx.append(self.battery)
            self.route_idx.append(self.shortest_path[i])
            self.status_idx.append(self.status)
            self.ev_time_idx.append(self.ev_time)
            i+=1
            if i == len(self.shortest_path)-1:
                break


        self.model.grid.move_agent(self,self.target_pos)
        try:
          edge = g.get_eid(self.shortest_path[i - 1], self.target_pos)
          self.travelled_dis = g.es[edge]['length']
          self.distance_idx.append(self.travelled_dis)
        except ig.InternalError as e:
          self.travelled_dis = self.travelled_dis
          self.distance_idx.append(self.travelled_dis)

        self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
        self.ev_time = self.ev_time + self.travelled_dis/self.speed
        self.status = 'finish'
        self.battery = self.battery - self.travelled_dis*self.consum_rate
        self.route_idx.append(self.dest)
        self.status_idx.append(self.status)
        self.battery_idx.append(self.battery)
        self.ev_time_idx.append(self.ev_time)
        self.current_pos = self.target_pos
        #self.trip_plan.remove(next((d for d in self.trip_plan if self.current_trip_id in d)))
        self.trip_left -=1
        self.trip_idx +=1
        self.evaluate_soc()

    def evaluate_soc(self):
        self.diary.append('evaluate_soc')
        if self.battery <= self.full_battery * self.soc_threshold:
            self.ask_for_stations()
        else:
            self.activity()

    def activity (self):
        self.diary.append('activity')
        self.status = 'activity'
        self.status_idx.append(self.status)
        if self.trip_left >0:
            self.current_trip = self.trip_plan[self.trip_idx]
            self.trip_start_time = list(self.current_trip.values())[0][2]
            if self.ev_time < self.trip_start_time:
                self.status = 'ready for next trip'
                self.status_idx.append(self.status)
                self.ev_time = self.trip_start_time
                self.ev_time_idx.append(self.ev_time)
            else:
                self.status = 'late for next trip'
                self.status_idx.append(self.status)
                self.ev_time_idx.append(self.ev_time)
            self.evaluation()
        else:
            self.status = 'finish all day'
            self.status_idx.append(self.status)

    def ask_for_stations(self):
        self.diary.append('ask_for_stations')
        self.pos_lon, self.pos_lat = self.model.id_mapping[str(self.current_pos)]
        self.current_coor = np.array([self.pos_lat, self.pos_lon])
        self.candidate_stations = []
        self.distance_dict = {}
        self.candidate_stations, self.distance_dict = self.model.get_candidate_stations(self.current_pos, self.current_coor, 500, self.ev_time, float('inf'))
        if len(self.candidate_stations) >0:
            self.choose_dwell_station()
            self.charge_dwell()
        else:
            self.activity()

    def choose_dwell_station (self):
        self.diary.append('choose_dwell_station')
        self.candidate_stations_info = {key: self.model.station_info[key] for key in self.candidate_stations if key in self.model.station_info}
        self.candidate_station_keys = list(self.candidate_stations_info.keys())
        self.candidate_station_speed_list = [value[1] for value in self.candidate_stations_info.values()]
        if self.trip_left > 0:
            self.trip_start_time = list(self.trip_plan[0].values())[0][2]
            self.stay_time = self.trip_start_time - self.ev_time
            self.charge_amount_list = [self.stay_time * a for a in list(set(self.candidate_station_speed_list))]

            if max(self.charge_amount_list) + self.battery < self.full_battery:
                self.cost_results = {}
                for charge_amount in self.charge_amount_list:
                    for i, [price, speed, init_park, add_park] in self.candidate_stations_info.items():
                        self.charge_time_record = charge_amount / speed
                        if self.charge_time_record <= 1:
                            self.station_cost = self.alpha * charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park
                        else:
                            self.station_cost = self.alpha * charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park + self.alpha * (self.charge_time_record-1) * add_park

                        self.cost_results[(charge_amount, i)] = self.station_cost

                self.chosen_amount_station = min(self.cost_results, key=self.cost_results.get)
                self.chosen_charge_amount, self.chosen_station = self.chosen_amount_station
                self.chosen_price = self.candidate_stations_info[self.chosen_station][0]
                self.chosen_speed = self.candidate_stations_info[self.chosen_station][1]
                self.chosen_init_park = self.candidate_stations_info[self.chosen_station][2]
                self.chosen_add_park = self.candidate_stations_info[self.chosen_station][3]

            else:
                self.chosen_charge_amount = self.full_battery - self.battery
                self.cost_results = {}
                for i, [price, speed, init_park, add_park] in self.candidate_stations_info.items():
                    self.charge_time_record = self.chosen_charge_amount / speed
                    if self.charge_time_record <= 1:
                        self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park
                    else:
                        self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park + self.alpha * (self.charge_time_record-1) * add_park

                    self.cost_results[i] = self.station_cost
                    self.chosen_station = min(self.cost_results, key=self.cost_results.get)
                    self.chosen_price = self.candidate_stations_info[self.chosen_station][0]
                    self.chosen_speed = self.candidate_stations_info[self.chosen_station][1]
                    self.chosen_init_park = self.candidate_stations_info[self.chosen_station][2]
                    self.chosen_add_park = self.candidate_stations_info[self.chosen_station][3]

        else:
            self.chosen_charge_amount = self.full_battery - self.battery
            self.cost_results = {}
            for i, [price, speed, init_park, add_park] in self.candidate_stations_info.items():
                self.charge_time_record = self.chosen_charge_amount / speed
                if self.charge_time_record <= 1:
                    self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park
                else:
                    self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.alpha * init_park + self.alpha * (self.charge_time_record-1) * add_park

                self.cost_results[i] = self.station_cost
                self.chosen_station = min(self.cost_results, key=self.cost_results.get)
                self.chosen_price = self.candidate_stations_info[self.chosen_station][0]
                self.chosen_speed = self.candidate_stations_info[self.chosen_station][1]
                self.chosen_init_park = self.candidate_stations_info[self.chosen_station][2]
                self.chosen_add_park = self.candidate_stations_info[self.chosen_station][3]

    def charge_dwell(self):
        self.diary.append('charge_dwell')
        self.status = 'charge dwell'
        self.status_idx.append('charge dwell')
        self.charge_time_length = self.chosen_charge_amount/self.chosen_speed
        self.expect_charge_end_time = self.ev_time + self.charge_time_length
        self.model.take_up_station(self.chosen_station, self.ev_time, self.expect_charge_end_time)

        self.ev_time = self.expect_charge_end_time
        self.ev_time_idx.append(self.ev_time)

        self.battery = self.battery + self.chosen_charge_amount
        self.battery_idx.append(self.battery)

        if self.charge_time_length <= 1:
            self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park
        else:
            self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park + (self.charge_time_length-1)*self.chosen_add_park

        self.used_station.append(self.chosen_station)
        self.finance_idx.append(self.payment)
        self.time_charge_idx.append(self.charge_time_length)

        self.activity()

    def charge_plan(self):
        self.diary.append('charge_plan')
        # It would be hard to define the radius a driver will search for. Plus, KDTree is not capable for searching the en-route distance.
        # A driver can be more desperate for charging than the driver who has arrived at the destination.
        # It is therefore assumed that a driver will look for the five nearest stations and make his choice.
        self.status = 'charge plan'
        self.status_idx.append(self.status)
        self.pos_lon, self.pos_lat = self.model.id_mapping[str(self.current_pos)]
        self.current_coor = np.array([self.pos_lat, self.pos_lon])
        self.capable_distance =  self.battery/self.consum_rate
        self.desperate_number = 1

        self.candidate_stations =[]
        while self.candidate_stations == []:
            self.candidate_stations, self.candidate_distance_dict = self.model.get_candidate_stations_desperate(self.current_pos, self.current_coor, self.desperate_number, self.ev_time, self.capable_distance)
            self.desperate_number +=1
            if self.desperate_number > 2:
                break

        if self.desperate_number > 2:
          self.status = 'fail trip when start'
          self.status_idx.append(self.status)

        else:
          if self.charge_need_to_dest + self.battery < self.soc_threshold*self.full_battery:
            self.chosen_charge_amount = self.soc_threshold*self.full_battery - self.battery
          else:
            self.chosen_charge_amount = self.charge_need_to_dest

          self.candidate_stations_info = {key: self.model.station_info [key] for key in self.candidate_stations if key in self.model.station_info}
          self.candidate_station_keys = self.candidate_stations
          self.cost_results = {}
          for i, [price, speed, init_park, add_park] in self.candidate_stations_info.items():
            self.charge_time_record = self.chosen_charge_amount / speed
            if self.charge_time_record <= 1:
                self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.beta* self.candidate_distance_dict[i]/self.speed + self.alpha * init_park
            else:
                self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.beta* self.candidate_distance_dict[i]/self.speed + self.alpha * init_park + self.alpha * (self.charge_time_record-1) * add_park

            self.cost_results[i] = self.station_cost

          self.chosen_station = min(self.cost_results, key=self.cost_results.get)
          self.chosen_price = self.candidate_stations_info[self.chosen_station][0]
          self.chosen_speed = self.candidate_stations_info[self.chosen_station][1]
          self.chosen_init_park = self.candidate_stations_info[self.chosen_station][2]
          self.chosen_add_park = self.candidate_stations_info[self.chosen_station][3]
          #print(self.chosen_station)
          self.drive_to_selected_station()

    def drive_to_selected_station (self):
        self.diary.append('drive_to_selected_station')
        self.target_pos = self.model.station_node[self.chosen_station]
        self.shortest_path_to_station = g.get_shortest_path(v = self.current_pos, to = int(self.target_pos), weights = g.es['length'], output = 'vpath')
        self.shortest_path_length_to_station = (g.distances(source = self.current_pos, target = int(self.target_pos), weights = 'length'))[0][0]

        i = 1
        self.status = 'drive'
        while i < len(self.shortest_path_to_station):
            self.model.grid.move_agent(self, self.shortest_path_to_station[i])
            self.current_pos = self.shortest_path_to_station[i]
            edge = g.get_eid(self.shortest_path_to_station[i - 1], self.shortest_path_to_station[i])
            self.travelled_dis = g.es[edge]['length']
            self.distance_idx.append(self.travelled_dis)
            self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
            self.ev_time = self.travelled_dis/self.speed + self.ev_time
            self.battery = self.battery - self.travelled_dis*self.consum_rate
            self.battery_idx.append(self.battery)
            self.route_idx.append(self.shortest_path_to_station[i])
            self.status_idx.append(self.status)
            self.ev_time_idx.append(self.ev_time)
            # check the availablity status every time of move
            rounded_ev_time = ((self.ev_time + 14) // 15) * 15
            station_int = int(self.chosen_station.replace('_', ''))
            availability_key = f"{station_int}_{int(rounded_ev_time)}"
            if self.model.station_avail.get(availability_key) == 1:
                self.consider_reselect_station()
                break
            else:
                i+=1
                if i == len(self.shortest_path_to_station)-1:
                    break

        self.model.grid.move_agent(self,int(self.target_pos))
        try:
          edge = g.get_eid(self.shortest_path_to_station[i - 1], int(self.target_pos))
          self.travelled_dis = g.es[edge]['length']
          self.distance_idx.append(self.travelled_dis)
        except ig.InternalError as e:
          self.travelled_dis = self.travelled_dis
          self.distance_idx.append(self.travelled_dis)
        except IndexError as e:
          self.travelled_dis = self.travelled_dis
          self.distance_idx.append(self.travelled_dis)

        self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
        self.battery = self.battery - self.travelled_dis*self.consum_rate
        self.ev_time = self.travelled_dis/self.speed + self.ev_time
        self.status = 'arrive at station on road'
        self.battery_idx.append(self.battery)
        self.ev_time_idx.append(self.ev_time)
        self.status_idx.append(self.status)
        self.charge_en_route()

    def consider_reselect_station (self):
        self.diary.append('consider_reselect_station')
        self.pos_lon, self.pos_lat = self.model.id_mapping[str(self.current_pos)]
        self.current_coor = np.array([self.pos_lat, self.pos_lon])
        self.capable_distance =  self.battery/self.consum_rate

        self.desperate_number = 1
        self.candidate_stations =[]
        while self.candidate_stations == []:
            self.candidate_stations, self.candidate_distance_dict = self.model.get_candidate_stations_desperate(self.current_pos, self.current_coor, self.desperate_number, self.ev_time, self.capable_distance)
            self.desperate_number +=1
            if self.desperate_number > 2:
                break

        if self.candidate_stations == []:
            self.drive_to_planned_station()
        else:
            if self.charge_need_to_dest + self.battery < self.soc_threshold*self.full_battery:
                self.chosen_charge_amount = self.soc_threshold*self.full_battery - self.battery
            else:
                self.chosen_charge_amount = self.charge_need_to_dest
            self.candidate_stations_info = {key: self.model.station_info [key] for key in self.candidate_stations if key in self.model.station_info}
            self.candidate_station_keys = self.candidate_stations
            self.cost_results = {}
            for i, [price, speed, init_park, add_park] in self.candidate_stations_info.items():
                self.charge_time_record = self.chosen_charge_amount / speed
                if self.charge_time_record <= 1:
                    self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.beta* self.candidate_distance_dict[i]/self.speed + self.alpha * init_park
                else:
                    self.station_cost = self.alpha * self.chosen_charge_amount * price + self.beta * self.charge_time_record + self.beta* self.candidate_distance_dict[i]/self.speed + self.alpha * init_park + self.alpha * (self.charge_time_record-1) * add_park

                self.cost_results[i] = self.station_cost

            self.chosen_station = min(self.cost_results, key=self.cost_results.get)
            self.chosen_price = self.candidate_stations_info[self.chosen_station][0]
            self.chosen_speed = self.candidate_stations_info[self.chosen_station][1]
            self.chosen_init_park = self.candidate_stations_info[self.chosen_station][2]
            self.chosen_add_park = self.candidate_stations_info[self.chosen_station][3]

            self.drive_to_selected_station()

    def drive_to_planned_station(self):
        self.diary.append('drive_to_planned_station')
        self.shortest_path_to_station = g.get_shortest_path(v = self.current_pos, to = int(self.target_pos), weights = g.es['length'], output = 'vpath')
        self.shortest_path_length_to_station = (g.distances(source = self.current_pos, target = int(self.target_pos), weights = 'length'))[0][0]

        i = 0
        while i < len(self.shortest_path_to_station):
            self.model.grid.move_agent(self, self.shortest_path_to_station[i])
            self.current_pos = self.shortest_path_to_station[i]
            if i > 0:
              edge = g.get_eid(self.shortest_path_to_station[i - 1], self.shortest_path_to_station[i])
              self.travelled_dis = g.es[edge]['length']
            else:
              self.travelled_dis =0
            self.distance_idx.append(self.travelled_dis)
            self.ev_time = self.travelled_dis/self.speed + self.ev_time
            self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
            self.battery = self.battery - self.travelled_dis*self.consum_rate
            self.battery_idx.append(self.battery)
            self.route_idx.append(self.shortest_path_to_station[i])
            self.status_idx.append(self.status)
            self.ev_time_idx.append(self.ev_time)
            i+=1
            if i == len(self.shortest_path)-1:
                break

        self.model.grid.move_agent(self,int(self.target_pos))
        try:
          edge = g.get_eid(self.shortest_path_to_station[i - 1], int(self.target_pos))
          self.travelled_dis = g.es[edge]['length']
          self.distance_idx.append(self.travelled_dis)
        except ig.InternalError as e:
          self.travelled_dis = self.travelled_dis
          self.distance_idx.append(self.travelled_dis)

        self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
        self.ev_time = self.ev_time + self.travelled_dis/self.speed
        self.status = 'arrive at station en route'
        self.battery = self.battery - self.travelled_dis*self.consum_rate
        self.charge_need_to_dest =  self.charge_need_to_dest - self.travelled_dis*self.consum_rate
        self.route_idx.append(self.dest)
        self.status_idx.append(self.status)
        self.battery_idx.append(self.battery)
        self.ev_time_idx.append(self.ev_time)
        self.current_pos = self.target_pos

        self.charge_en_route()

    def charge_en_route(self):
        self.diary.append('charge_en_route')
        rounded_ev_time = ((self.ev_time + 14) // 15) * 15
        station_int = int(self.chosen_station.replace('_', ''))
        availability_key = f"{station_int}_{int(rounded_ev_time)}"
        if self.model.station_avail.get(availability_key) == 0:
          self.status = 'charge'
          self.charge_start_time = self.ev_time
          self.battery = self.battery + self.chosen_charge_amount
          self.charge_end_time = self.ev_time + self.chosen_charge_amount/self.chosen_speed
          self.ev_time = self.charge_end_time
          self.status_idx.append(self.status)
          self.battery_idx.append(self.battery)
          self.ev_time_idx.append(self.ev_time)

          if self.chosen_charge_amount/self.chosen_speed <= 1:
              self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park
          else:
              self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park + (self.chosen_charge_amount/self.chosen_speed-1)*self.chosen_add_park

          self.finance_idx.append(self.payment)
          self.time_charge_idx.append(self.chosen_charge_amount/self.chosen_speed)
          self.used_station.append(self.chosen_station)

          self.model.take_up_station(self.chosen_station, self.charge_start_time, self.charge_end_time)

          self.status = 'finish charge'
          self.status_idx.append(self.status)
          self.current_pos = self.model.station_node[self.chosen_station]
          self.target_pos = self.dest
          self.shortest_path = g.get_shortest_path(v = int(self.current_pos), to = self.target_pos, weights = g.es['length'], output = 'vpath')
          self.shortest_path_length = (g.distances(source = self.orig, target = self.dest, weights = 'length'))[0][0]

          self.drive_to_destination()
        else:
          self.queue()

    def queue(self):
        self.diary.append('queue')
        self.pos_lon, self.pos_lat = self.model.id_mapping[str(self.current_pos)]
        self.current_coor = np.array([self.pos_lat, self.pos_lon])
        self.capable_distance =  self.battery/self.consum_rate
        self.desperate_number = 1
        self.candidate_stations =[]
        while self.candidate_stations == []:
            self.candidate_stations, _ = self.model.get_candidate_stations_desperate(int(self.current_pos), self.current_coor, self.desperate_number, self.ev_time, self.capable_distance)
            self.desperate_number +=1
            if self.desperate_number > 2:
                break

        if self.candidate_stations ==[]:
            self.queue_and_charge()
        else:
            self.queue_choices = ['queue', 'drive away']
            self.queue_choice = random.choice(self.queue_choices)
            if self.queue_choice == 'queue':
                self.queue_and_charge()
            else:
                self.status = 'stop queue and drive away'
                self.status_idx.append(self.status)
                self.chosen_station = self.candidate_stations[0]
                #print(self.chosen_station)
                self.drive_to_selected_station()

    def queue_and_charge(self):
        self.diary.append('queue_and_charge')
        self.status = 'queue'
        self.status_idx.append(self.status)
        self.charge_start_time = self.model.get_queue_finish_time(self.ev_time, self.chosen_station)
        self.charge_end_time = self.charge_start_time +self.chosen_charge_amount/self.chosen_speed
        self.model.take_up_station(self.chosen_station, self.charge_start_time, self.charge_end_time)

        if self.chosen_charge_amount/self.chosen_speed <= 1:
            self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park
        else:
            self.payment = self.chosen_price*self.chosen_charge_amount + self.chosen_init_park + (self.chosen_charge_amount/self.chosen_speed-1)*self.chosen_add_park

        self.finance_idx.append(self.payment)
        self.time_charge_idx.append(self.charge_start_time - self.ev_time)
        self.time_charge_idx.append(self.chosen_charge_amount/self.chosen_speed)
        self.used_station.append(self.chosen_station)

        self.status = 'charge after queue'
        self.status_idx.append(self.status)
        self.battery = self.battery + self.chosen_charge_amount
        self.battery_idx.append(self.battery)
        self.ev_time = self.charge_end_time
        self.ev_time_idx.append(self.ev_time)

        self.current_pos = self.model.station_node[self.chosen_station]
        self.target_pos = self.dest
        self.drive_to_destination()

    def cost_calculation(self):
        # time cost comes from driving time and the time spent at charger (charge and queue)
        self.distance_cost_value =sum(self.distance_idx)
        self.time_cost_value = self.distance_cost_value/self.speed
        self.charge_time_value_record = sum(self.time_charge_idx)
        self.time_cost_value += sum(self.time_charge_idx)

        #finance cost comes from the the payment for charger
        self.finance_cost_value = sum(self.finance_idx)
        self.total_cost = self.beta*self.time_cost_value + self.alpha*self.finance_cost_value

        self.distance_cost_idx.append(self.distance_cost_value)
        self.charge_time_record_idx.append(self.charge_time_value_record)
        self.total_time_idx.append(self.time_cost_value)
        self.total_cost_idx.append(self.total_cost)
        self.total_finance_idx.append(self.finance_cost_value)


    def step(self):
        self.initialisation()
        self.evaluation()
        self.cost_calculation()

class EV_Model(Model):
    def __init__(
        self, output_path:str,
        EV_agent:Optional[pd.DataFrame] = None,
        station_location:Optional[dict] = None,
        station_info: Optional[dict] = None,
        station_avail: Optional[dict] = None,
        station_node: Optional[dict] = None,
        id_mapping: Optional[dict] = None,
        g: Optional[igraph.Graph] = None,
        edge_lengths: Optional[dict] = None,
        networkx_graph:Optional[nx.Graph] = None):

        super().__init__()
        self.schedule = mesa.time.SimultaneousActivation(self)
        self.EV_agent = EV_agent #
        self.station_location = station_location #
        self.station_info = station_info #
        # self.station_avail = station_avail #
        self.station_node = station_node #
        self.id_mapping = id_mapping #
        self.g = g #
        self.edge_lengths = edge_lengths #
        self.networkx_graph = networkx_graph
        self.grid = NetworkGrid(self.networkx_graph)

        self.location_list = list(station_location.values())
        self.tree = cKDTree(self.location_list)

        self.station_avail_snapshots = {}
        self.original_station_avail = station_avail

        for index, row in EV_agent.iterrows():
            e = EV(row['IndividualID'], row['full_battery'], row['consum_rate'], row['soc_threshold'],
                    row['trip_plan_new'], row['alpha'], row['beta'], self)
            self.schedule.add(e)
            self.grid.place_agent(e, row['o_osmid'])

        self.data_collector = DataCollector(
            model_reporters={
            },
            agent_reporters={
                'unique_id': lambda a: a.unique_id if a.agent_type =='EV'else None,
                'status_idx' : lambda a: a.status_idx if a.agent_type =='EV'else None,
                'battery_idx' : lambda a: a.battery_idx if a.agent_type =='EV'else None,
                'route_idx' : lambda a: a.route_idx if a.agent_type =='EV'else None,
                'ev_time_idx' : lambda a: a.ev_time_idx if a.agent_type =='EV'else None,
                'ev_diary' : lambda a: a.diary if a.agent_type =='EV'else None,
                'alpha':lambda a: a.alpha if a.agent_type =='EV'else None,
                'speed':lambda a: a.speed if a.agent_type =='EV'else None,
                'time_cost_value':lambda a: a.time_cost_value if a.agent_type =='EV'else None,
                'time_charge_idx':lambda a: a.time_charge_idx if a.agent_type =='EV'else None,
                'finance_idx':lambda a: a.finance_idx if a.agent_type =='EV'else None,
                'total_finance_idx':lambda a: a.total_finance_idx if a.agent_type =='EV'else None,
                'total_time_idx':lambda a: a.total_time_idx if a.agent_type =='EV'else None,
                'total_cost_idx':lambda a: a.total_cost_idx if a.agent_type =='EV'else None,
                'orig':lambda a: a.orig if a.agent_type =='EV'else None,
                'dest':lambda a: a.dest if a.agent_type =='EV'else None,
                'soc_threshold':lambda a: a.soc_threshold if a.agent_type =='EV'else None,
                'init_soc_random':lambda a: a.init_soc_random if a.agent_type =='EV'else None,
                'full_battery':lambda a: a.full_battery if a.agent_type =='EV'else None,
                'consum_rate':lambda a: a.consum_rate if a.agent_type =='EV'else None,
                'distance_travelled':lambda a: a.distance_cost_idx if a.agent_type =='EV'else None,
                'charge_time_used':lambda a: a.charge_time_record_idx if a.agent_type =='EV'else None,
                'used_station':lambda a: a.used_station if a.agent_type =='EV'else None
                }
                )

    def get_candidate_stations(self, current_node, current_coor, radius, ev_time, max_dist):
        rounded_ev_time = ((ev_time + 14) // 15) * 15
        indices = self.tree.query_ball_point(current_coor, radius/111000, p=2)
        if isinstance(indices, np.ndarray):
          indices = indices.tolist()
        elif not isinstance(indices, list):
          indices = [indices]
        all_candidate_stations = [list(self.station_location.keys())[i] for i in indices]
        all_candidate_stations_node = [self.station_node[key] for key in all_candidate_stations if key in self.station_node]
        all_candidate_stations_node = [int(item) for item in all_candidate_stations_node]

        all_candidate_stations_distances = []
        for node in all_candidate_stations_node:
          distance = (g.distances (source = current_node, target = node, weights = 'length'))[0][0]
          all_candidate_stations_distances.append(distance)
        # all_candidate_stations_distances = (g.distances (source = current_node, target = all_candidate_stations_node, weights = 'length'))[0]
        distance_dict = dict(zip(all_candidate_stations, all_candidate_stations_distances))

        available_stations = []
        for station in all_candidate_stations:
          station_int = station_int = int(station.replace('_', ''))
          availability_key = f"{station_int}_{int(rounded_ev_time)}"
          # a = distance_dict[station]
          if self.station_avail.get(availability_key) == 0:
            if distance_dict[station] <= max_dist:
                available_stations.append(station)

        return available_stations, distance_dict

    def get_candidate_stations_desperate (self, current_node, current_coor, number, ev_time, max_dist):
        rounded_ev_time = ((ev_time + 14) // 15) * 15
        _, indices = self.tree.query(current_coor, k = number)
        if isinstance(indices, np.ndarray):
          indices = indices.tolist()
        elif not isinstance(indices, list):
          indices = [indices]

        all_candidate_stations = [list(self.station_location.keys())[i] for i in indices]
        all_candidate_stations_node = list([self.station_node[key] for key in all_candidate_stations if key in self.station_node])
        all_candidate_stations_node = [int(item) for item in all_candidate_stations_node]

        all_candidate_stations_distances = []
        for node in all_candidate_stations_node:
          distance = (g.distances (source = current_node, target = node, weights = 'length'))[0][0]
          all_candidate_stations_distances.append(distance)

        distance_dict = dict(zip(all_candidate_stations, all_candidate_stations_distances))
        candidate_stations =[]
        for station in all_candidate_stations:
          station_int = int(station.replace('_', ''))
          availability_key = f"{station_int}_{int(rounded_ev_time)}"
          if self.station_avail.get(availability_key) == 0:
             if distance_dict[station] <= max_dist:
                candidate_stations.append(station)

        return candidate_stations, distance_dict

    def get_queue_finish_time(self, ev_time, station_id):
        port_id = int(station_id.replace('_', ''))
        rounded_ev_time = ((ev_time + 14) // 15) * 15
        for time_slot in range(rounded_ev_time, 14400 + 1, 15):
           availability_key = f"{port_id}_{time_slot}"
           if self.station_avail.get(availability_key) == 0:
              return time_slot

    def take_up_station(self, station_id, ev_time, expect_charge_end_time):
        port_id = int(station_id.replace('_', ''))
        rounded_ev_time = int(((ev_time + 14) // 15) * 15)
        rounded_end_time = int(((expect_charge_end_time + 14) // 15) * 15)
        rounded_end_time  +=15
        for time in range(rounded_ev_time, rounded_end_time, 15):
           availability_key = f"{port_id}_{time}"
           self.station_avail[availability_key] = 1

    def reset_station_avail(self):
        self.station_avail = self.original_station_avail.copy()

    def save_station_avail_snapshot(self, step: int):
        self.station_avail_snapshots[step] = self.station_avail.copy()

    def step(self):
        self.schedule.step()
        self.data_collector.collect(self)
        self.save_station_avail_snapshot(self.schedule.steps)

    def run(self, steps: int):
        self.data_collector.collect(self)
        for k in range(steps):
            self.reset_station_avail()
            self.step()
        return self.data_collector.get_agent_vars_dataframe()

EVmodel = EV_Model('trail1', EV_agent = EV_agent, station_location = station_location, station_info = station_info, station_avail = station_avail,
                   station_node = station_node, id_mapping = id_mapping, g = g, edge_lengths = edge_lengths, networkx_graph = networkx_graph)

df = EVmodel.run(steps = 5)
df.to_pickle(r'/home/ec2-user/ABM_model/df_output_5times-1.pkl')
update_avail = EVmodel.station_avail_snapshots
with open(r'/home/ec2-user/ABM_model/update_avail_5times-1.pkl', 'wb') as f:
    pickle.dump(update_avail, f)
with open(r'/home/ec2-user/ABM_model/update_avail_5times-1.json', 'w') as f:
    json.dump(update_avail, f, indent=4)
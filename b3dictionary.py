#!/usr/bin/python

####################################################################################################################
#   B-Tree Dictionary                                                                    author: Ticiano Benetti   #
####################################################################################################################
#                                                                                                                  #
# Description: This class implements a common dictionary in python, with a B-tree behind it. Tests show that it's  #
#              eight times faster than grep for search. I have tested it up to 100 million keys.                   #
#                                                                                                                  #
# Features:                                                                                                        #
#           - Node cache to save disk seeks with hit ratio of 40%                                                  #
#           - Ballance in thread and split/merge modes                                                             #
#           - Statistics for splits, merges, keys, levels, cache hit and miss, thread ballances to left and right. #
#           - Behaves as iterator, in both direct and reverse order                                                #
#           - On insertion, if key already exists, it will update data                                             #
#           - On deletion and read, if key doen't exist, raises exception                                          #
#           - Consistency check when using an existing b-tree                                                      #
#           - Stores data as JSON                                                                                  #
#           - Keeps track and reuses free space to avoid fragmentation. Shrinks file if too many free space.       #
#                                                                                                                  #
# Usage:                                                                                                           #
#           - Open existing tree file:  my_tree = b3dict( filename )                                               #
#           - Create new tree file:     my_tree = b3dict( filename, num_keys, key_size, data_size )                #
#           - Adding or Updating:       my_tree[key] = data                                                        #
#           - Removing items:           del my_tree[key]                                                           #
#           - Reading data              data  = my_tree[key]                                                       #
#           - Iterate in direct order:  for key in my_tree:                                                        #
#           - Iterate in reverse order: for key in reversed( my_tree ):                                            #
#                                                                                                                  #
# Methods:                                                                                                         #
#           - check_consistency()       Scans the tree looking for inconsistencies in pointers and keys.           #
#           - stats()                   Returns dictionary with all the statistics.                                #
#                                                                                                                  #
####################################################################################################################

from collections.abc import MutableMapping
from os.path import exists
from math import trunc
import json

class b3dict( MutableMapping ):

    def __init__( self, file_name:str = 'b3dict.b3', num_keys:int = 512, key_size:int = 64, data_size:int = 256 ):

        corrupt = False

        # Iterator
        self.__iter_node = None
        self.__iter_dir = 'direct'
        self.__iter_pos = 0

        # Node cache
        self.__node_cache = []
        self.__cache_size = 32
        
        # Manual limits
        self.__min_num_keys = 3
        self.__max_num_keys = 1024
        self.__min_key_size = 1
        self.__max_key_size = 1024
        self.__min_data_size = 1
        self.__max_data_size = 4096
        self.__max_free_nodes = 10
        self.__max_offset_digits = 14 # ext4 max file size is 16T, which takes 14 digits to address.
        self.__empty_tree_header_size = 249 # With stats
        self.__empty_node_size = 100
        
        # Check parameter types
        if not isinstance( file_name, str ):
            raise TypeError( '<file_name> must be a str.' )
        if not isinstance( num_keys, int ):
            raise TypeError( '<num_keys> must be an int.' )
        if not isinstance( key_size, int ):
            raise TypeError( '<key_size> must be an int.' )
        if not isinstance( data_size, int ):
            raise TypeError( '<data_size> must be an int.' )
        
        # Check parameter values
        if num_keys > self.__max_num_keys or num_keys < self.__min_num_keys:
            raise ValueError( '<num_keys> must be between '+str(self.__min_num_keys)+' and '+str(self.__max_num_keys) )
        if key_size > self.__max_key_size or key_size < self.__min_key_size:
            raise ValueError( '<key_size> must be between '+str(self.__min_key_size)+' and '+str(self.__max_key_size) )
        if data_size > self.__max_data_size or data_size < self.__min_data_size:
            raise ValueError( '<data_size> must be between '+str(self.__min_data_size)+' and '+str(self.__max_data_size) )

        # Set private attributes
        self.__file_name = file_name
        self.__min_occup = trunc( num_keys / 3 )

        # Calculate digits of limits
        self.__max_num_keys_digits = len(str(self.__max_num_keys))
        self.__max_key_size_digits = len(str(self.__max_key_size))
        self.__max_data_size_digits = len(str(self.__max_data_size))

        # Calculate buffer sizes
        self.__max_tree_header_size = self.__empty_tree_header_size
        self.__max_tree_header_size += self.__max_num_keys_digits
        self.__max_tree_header_size += self.__max_key_size_digits
        self.__max_tree_header_size += self.__max_data_size_digits
        self.__max_tree_header_size += self.__max_offset_digits
        self.__max_tree_header_size += self.__max_free_nodes * ( 2 + self.__max_offset_digits )
        self.__max_tree_header_size += 7 * 20

        # If file exists Load header
        if exists( self.__file_name ):
            try:
                fd = open( self.__file_name, 'r' )
                self.__tree_header = json.loads( fd.readline() )
                fd.close()
                # Calculate buffer sizes
                self.__max_node_size = self.__empty_node_size
                self.__max_node_size += (3 * self.__max_offset_digits)
                self.__max_node_size +=  self.__tree_header['num_keys'] * (self.__tree_header['key_size'] + 2)
                self.__max_node_size +=  self.__tree_header['num_keys'] * (self.__tree_header['data_size'] + 2)
                self.__max_node_size +=  ( self.__tree_header['num_keys'] + 1 ) * (self.__max_offset_digits + 2)

            except json.decoder.JSONDecodeError:
                corrupt = True
                
            # Check tree consistency
            if not self.check_consistency():
                corrupt = True

        # Otherwise create file with header
        else:
            self.__tree_header = {
                'num_keys': num_keys,
                'key_size': key_size,
                'data_size': data_size,
                'root_offset': self.__max_tree_header_size + 1,
                'free_offset': [],
                'last_offset': self.__max_tree_header_size + 1,
                'stats': {
                    'nodes': 1,
                    'keys': 0,
                    'splits': 0,
                    'merges': 0,
                    'threads to left': 0,
                    'threads to right': 0,
                    'levels': 1,
                    'cache hit': 0,
                    'cache miss': 0
                }
            }
            fd = open( self.__file_name, 'w' )
            self.__save_header__( fd )
            new_node = {
                'offset': self.__tree_header['root_offset'],
                'upper_node': 0,
                'left_node': 0,
                'right_node': 0,
                'key': [],
                'data': [],
                'lower_node': []
            }
            
            # Calculate buffer sizes
            self.__max_node_size = self.__empty_node_size
            self.__max_node_size += (3 * self.__max_offset_digits)
            self.__max_node_size +=  self.__tree_header['num_keys'] * (self.__tree_header['key_size'] + 2)
            self.__max_node_size +=  self.__tree_header['num_keys'] * (self.__tree_header['data_size'] + 2)
            self.__max_node_size +=  ( self.__tree_header['num_keys'] + 1 ) * (self.__max_offset_digits + 2)

            self.__save_node__( fd, new_node )

        fd.close()

        # Raise exception if corrupt
        if corrupt:
            raise RuntimeError('B-Tree file is corrupt')

        # Calculate minimum occupation
        self.__min_occup = trunc( self.__tree_header['num_keys'] / 3 )

    # ----------------------------------------------------------------------

    def __save_header__( self, fd ):
        fd.seek( 0 )
        fd.write( json.dumps( self.__tree_header ).ljust( self.__max_tree_header_size, ' ' ) + '\n' )

        
    # ----------------------------------------------------------------------

    def __save_node__( self, fd, node ):

        # Update cache
        for cached_record in self.__node_cache:
            if cached_record['offset'] == node['offset']:
                cached_record['node'] = node.copy()

        # Save to disk
        fd.seek( node['offset'] )
        fd.write( json.dumps( node ).ljust( self.__max_node_size, ' ' ) )

    # ----------------------------------------------------------------------

    def __load_node__( self, fd, offset ):

        corrupt = False
        result = None

        # Check for cache hit
        for cached_record in self.__node_cache:
            if cached_record['offset'] == offset:

                # Statistics
                cached_record['hits'] += 1
                self.__tree_header['stats']['cache hit'] += 1

                # Return cached node
                return cached_record['node'].copy()

        # If not, cache miss
        self.__tree_header['stats']['cache miss'] += 1

        # Try to load node from disk
        try:
            fd.seek( offset )
            result = json.loads( fd.read( self.__max_node_size ) )

        # Unless its corrupt
        except json.decoder.JSONDecodeError:
            corrupt = True

        # If corrupt raise exception
        if corrupt:
            raise RuntimeError('B-Tree file is corrupt')

        # Moving on: If cache is full
        if len( self.__node_cache ) == self.__cache_size:

            # Find less used cached record
            min = 0
            for i in range( len( self.__node_cache ) ):
                if self.__node_cache[i]['hits'] < self.__node_cache[min]['hits']:
                    min = i

            # Remove it
            del self.__node_cache[min]

        # Add new record to cache
        self.__node_cache.append( { 'offset': offset, 'hits': 1, 'node': result.copy() } )
        
        return result
        
    # ----------------------------------------------------------------------

    def __binsearch__( self, key, lis, beg = 0 , _end = -1 ):

        # Default to whole list
        end = _end
        if end == -1:
            end = len( lis )
            
        # If empty list, return
        if beg == end:
            return beg

        # Calculate pivot position
        p = trunc( ( beg + end ) / 2 )

        # If key lower than pivot, recursively search lower half
        if key < lis[p]:
            return self.__binsearch__( key, lis, beg, p )

        # If key higher than pivot, recursively search higher half
        elif key > lis[p]:
            return self.__binsearch__( key, lis, p + 1, end )

        # Otherwise, found it.
        return p
    
    # ----------------------------------------------------------------------
        
    def __rec_search__( self, fd, offset, key ):

        corrupt = False
        
        # Initialize result
        result = { 'node': None,'position':0, 'exists': False }

        # Load node from disk
        result['node'] = self.__load_node__( fd, offset )

        # Search within keys
        result['position'] = self.__binsearch__( key, result['node']['key'] )
        
        # Test if found
        try:
            if result['node']['key'][result['position']] == key:
                result['exists'] = True
        except IndexError:
                result['exists'] = False

        # If found or if it's a leaf, return this node
        if result['exists'] or len(result['node']['lower_node']) == 0:
            return result 
                
        # Otherwise, do recursive call
        return self.__rec_search__( fd, result['node']['lower_node'][result['position']], key )


    # ----------------------------------------------------------------------

    def __free_node__( self, fd, node ):
        

        # Clear node
        node['upper_node'] = 0
        node['left_node'] = 0
        node['right_node'] = 0
        node['key'].clear()
        node['data'].clear()
        node['lower_node'].clear()
        
        # Save node
        self.__save_node__( fd, node )

        # Register free node
        self.__tree_header['free_offset'].append(node['offset'])
        self.__tree_header['free_offset'].sort()
        self.__save_header__( fd )

        # If too many free nodes
        if len( self.__tree_header['free_offset'] ) > self.__max_free_nodes:

            # Load last node in file
            last_node = self.__load_node__( fd, self.__tree_header['last_offset'] )

            # If last node is empty
            if len( last_node['key'] ) == 0:

                # Just remove last node from list of free offsets
                self.__tree_header['free_offset'].remove( self.__tree_header['last_offset'] )

            # Otherwise
            else:

                # Move node and remove
                new_offset = self.__tree_header['free_offset'].pop(0)
                self.__move_node__( fd, self.__tree_header['last_offset'], new_offset )

                # Update header if moving root
                if self.__tree_header['last_offset'] == self.__tree_header['root_offset']:
                    self.__tree_header['root_offset'] = new_offset

            # Shrink file
            fd.seek( self.__tree_header['last_offset'] )
            fd.truncate()

            # Update last_offset
            self.__tree_header['last_offset'] -= self.__max_node_size
            self.__save_header__( fd )

    # ----------------------------------------------------------------------

    def __alloc_node__( self, fd ):

        node = None
        
        try:
            # Get next free node
            node = self.__load_node__( fd, self.__tree_header['free_offset'].pop(0) )
            node['key'].clear()
            node['data'].clear()
            node['lower_node'].clear()
            
        except IndexError:
            # If no free nodes available, create one in the end
            fd.seek( 0, 2)
            node = {
                'offset': fd.tell(),
                'upper_node': 0,
                'left_node': 0,
                'right_node': 0,
                'key': [],
                'data': [],
                'lower_node': []
            }
            self.__tree_header['last_offset'] = node['offset']
            fd.write( json.dumps( node ).ljust( self.__max_node_size, ' ' ) )

        # Statistics
        self.__tree_header['stats']['nodes'] += 1
        self.__save_header__( fd )
        
        return node
    
    # ----------------------------------------------------------------------
    
    def __merge_node__( self, fd, offset ):

        # Load node
        node = self.__load_node__( fd, offset )

        # If root
        if offset == self.__tree_header['root_offset']:
            
            # If root is empty but with a lower node
            if len( node['key'] ) == 0 and len( node['lower_node'] ) > 0:

                # Set new root and do statistics
                self.__tree_header['root_offset'] = node['lower_node'][0]
                self.__tree_header['stats']['merges'] += 1
                self.__tree_header['stats']['levels'] -= 1
                self.__tree_header['stats']['nodes'] -= 1
                self.__save_header__( fd )
                
                # Free old root
                self.__free_node__( fd, node )
                
                # Fix new root
                sub = self.__load_node__( fd, self.__tree_header['root_offset'] )
                sub['upper_node'] = 0
                self.__save_node__( fd, sub )

            # Return
            return
        
        # Statistics
        self.__tree_header['stats']['merges'] += 1
        self.__save_header__( fd )
        
        # Load upper node
        upper_node = self.__load_node__( fd, node['upper_node'] )
        
        # Load left node
        left_node = None
        left_occup = self.__tree_header['num_keys']
        if node['left_node'] > 0:
            left_node = self.__load_node__( fd, node['left_node'] )
            left_occup = len( left_node['key'] )
            
        # Load right node
        right_node = None
        right_occup = self.__tree_header['num_keys']
        if node['right_node'] > 0:
            right_node = self.__load_node__( fd, node['right_node'] )
            right_occup = len( right_node['key'] )

        # Choose merge parties and set them to left and right
        if right_occup > left_occup:
            right_node = node
        else:
            left_node = node

        # Fix lower
        for off in right_node['lower_node']:
            sub = self.__load_node__( fd, off )
            sub['upper_node'] = left_node['offset']
            self.__save_node__( fd, sub )

        # Fix left & right on node's level
        left_node['right_node'] = right_node['right_node']
        if left_node['right_node'] > 0:
            new_right_node = self.__load_node__( fd, left_node['right_node'] )
            new_right_node['left_node'] = left_node['offset']
            self.__save_node__( fd, new_right_node )

        # Fix left & right on node's sub level
        if len( left_node['lower_node'] ) > 0:
            sub = self.__load_node__( fd, left_node['lower_node'][-1] )
            sub['right_node'] = right_node['lower_node'][0]
            self.__save_node__( fd, sub )
            sub = self.__load_node__( fd, right_node['lower_node'][0] )
            sub['left_node'] = left_node['lower_node'][-1]
            self.__save_node__( fd, sub )
        
        # Find position in upper node
        pos = self.__binsearch__( left_node['key'][-1], upper_node['key'] )

        # Bring key+data down and del pointer to right
        left_node['key'].append(upper_node['key'].pop(pos))
        left_node['data'].append(upper_node['data'].pop(pos))
        del upper_node['lower_node'][pos+1]

        # Merge 
        left_node['key'].extend( right_node['key'] )
        left_node['data'].extend( right_node['data'] )
        left_node['lower_node'].extend( right_node['lower_node'] )
        
        # Save nodes
        for n in [left_node, upper_node]:
            self.__save_node__( fd, n )

        # Free right node
        self.__free_node__( fd, right_node )

        # Statistics
        self.__tree_header['stats']['nodes'] -= 1
        self.__save_header__( fd )

        # Ballance upper
        if len( upper_node['key'] ) < self.__min_occup:
            if not self.__thread_ballance__( fd, upper_node['offset'] ):
                self.__merge_node__( fd, upper_node['offset'] )
        
    # ----------------------------------------------------------------------
    
    def __split_node__( self, fd, offset ):

        # Statistics
        self.__tree_header['stats']['splits'] += 1
        self.__save_header__( fd )

        # Calculate pivot position
        pivot = trunc( self.__tree_header['num_keys'] / 2 )

        # Load node to split, known as left node
        left_node = self.__load_node__( fd, offset )

        # Create new node, known right node - decided to always split to the right
        right_node = self.__alloc_node__( fd )
        
        # If we are splitting the root
        if offset == self.__tree_header['root_offset']:

            # Statistics
            self.__tree_header['stats']['levels'] += 1
            self.__save_header__( fd )
            
            # Create upper node (new root) and set first lower node. Second will come in pivot promotion
            upper_node = self.__alloc_node__( fd )
            upper_node['lower_node'].insert( 0, left_node['offset'] )
            
            # Update and save tree header
            self.__tree_header['root_offset'] = upper_node['offset']
            self.__save_header__( fd )
                        
        # Otherwise, just load upper node
        else:
            upper_node = self.__load_node__( fd, left_node['upper_node'] )
            
        # Promote pivot to upper node
        pos = self.__binsearch__( left_node['key'][pivot], upper_node['key'] )
        upper_node['key'].insert( pos, left_node['key'][pivot] )
        upper_node['data'].insert( pos, left_node['data'][pivot] )
        upper_node['lower_node'].insert( pos+1, right_node['offset'] )

        # Split key array and data array
        right_node['key'] = left_node['key'][pivot+1:]
        right_node['data'] = left_node['data'][pivot+1:]
        left_node['key'] = left_node['key'][:pivot]
        left_node['data'] = left_node['data'][:pivot]

        # Set new left, right and upper in the new node
        right_node['upper_node'] = upper_node['offset']
        right_node['left_node'] = left_node['offset']
        right_node['right_node'] = left_node['right_node']

        # Set new right and upper in the splitted node (upper update will be needed in root split)
        left_node['upper_node'] = upper_node['offset']
        left_node['right_node'] = right_node['offset']

        # If inherited right neighbor exists, update right neighbor's left_node pointer to new node
        if right_node['right_node'] > 0:
            rn = self.__load_node__( fd, right_node['right_node'] )
            rn['left_node'] = right_node['offset']
            self.__save_node__( fd, rn )

        # If splitted and new node have lower lower nodes
        if len( left_node['lower_node'] ) > 0:
            
            # split lower node pointer array
            right_node['lower_node'] = left_node['lower_node'][pivot+1:]
            left_node['lower_node'] = left_node['lower_node'][:pivot+1]

            # point upper node to new node in lower nodes moved to new node
            for off in right_node['lower_node']:
                sub = self.__load_node__( fd, off )
                sub['upper_node'] = right_node['offset']
                self.__save_node__( fd, sub )

            # Zero left neighbor of node pointed by pointer at [pivot+1] because now such pointer is on the left edge
            sub = self.__load_node__( fd, right_node['lower_node'][0] )
            sub['left_node']=0
            self.__save_node__( fd, sub )
            
            # Zero right neighbor of node pointed by pointer at [pivot-1] because now such pointer is on the right-most position
            sub = self.__load_node__( fd, left_node['lower_node'][-1] )
            sub['right_node']=0    
            self.__save_node__( fd, sub )

        # Save current node, new neighbor and new root
        for node in [left_node, right_node, upper_node]:
            self.__save_node__( fd, node )

        # Ballance upper node
        if len(upper_node['key']) == self.__tree_header['num_keys']:
            if not self.__thread_ballance__( fd, upper_node['offset'] ):
                self.__split_node__( fd, upper_node['offset'] )
    
    # ----------------------------------------------------------------------

    def __thread_ballance__( self, fd, offset ):

        ret = False
        direction = None
        giver = None
        taker = None

        # Load node
        node = self.__load_node__( fd, offset )
        occup = len( node['key'] )

        # Can't thread if I'm root
        if node['upper_node'] == 0:
            return ret
        
        # Load upper node
        upper_node = self.__load_node__( fd, node['upper_node'] )
        
        # Load left node
        left_node = None
        left_occup = 0
        if node['left_node'] > 0:
            left_node = self.__load_node__( fd, node['left_node'] )
            left_occup = len( left_node['key'] )

        # Load right node
        right_node = None
        right_occup = 0
        if node['right_node'] > 0:
            right_node = self.__load_node__( fd, node['right_node'] )
            right_occup = len( right_node['key'] )

        # If underflow
        if occup < self.__min_occup:

            # Node is the taker
            taker = node

            # If left node has less keys than node and less keys than right node then left is the taker
            if left_occup > 0 and left_occup > self.__min_occup and ( left_occup >= right_occup or right_occup == 0 ):
                giver = left_node
                direction = 'right'

            # Else, if right node has less keys than node and less keys than left node then right is the taker
            elif right_occup > 0 and right_occup > self.__min_occup and ( right_occup >= left_occup or left_occup == 0 ):
                giver = right_node
                direction = 'left'
            
        # Else, if node has enough to give
        elif occup > self.__min_occup:

            # Node is the giver
            giver = node

            # If left node has less keys than node and less keys than right node then left is the taker
            if left_occup > 0 and left_occup < ( occup - 1 ) and ( left_occup < right_occup or right_occup == 0 ):
                taker = left_node
                direction = 'left'

            # If right node has less keys than node and less keys than left node then right is the taker
            elif right_occup > 0 and right_occup < ( occup - 1 ) and ( right_occup < left_occup or left_occup == 0 ):
                taker = right_node
                direction = 'right'

        # Thread to left
        if direction == 'left':
            
            # Statistics
            self.__tree_header['stats']['threads to left'] += 1
            self.__save_header__( fd )

            # Find position in upper node
            pos = self.__binsearch__( giver['key'][0], upper_node['key'] ) - 1

            # Thread key and data
            for par in ['key', 'data']:
                taker[par].append( upper_node[par][pos] )
                upper_node[par][pos] = giver[par].pop(0)

            # If has lower nodes
            if len( giver['lower_node'] ) > 0:

                # Move pointer
                taker['lower_node'].append( giver['lower_node'].pop(0) )

                # Fix left & right for node at offset=ptr
                sub = self.__load_node__( fd, taker['lower_node'][-1] )
                sub['upper_node'] = taker['offset']
                sub['right_node'] = 0
                sub['left_node'] = taker['lower_node'][-2]
                self.__save_node__( fd, sub )

                # Fix left for ex right node
                sub = self.__load_node__( fd, giver['lower_node'][0] )
                sub['left_node'] = 0
                self.__save_node__( fd, sub )

                # Fix right for new left node
                sub = self.__load_node__( fd, taker['lower_node'][-2] )
                sub['right_node'] = taker['lower_node'][-1]
                self.__save_node__( fd, sub )
                
            ret = True

        # Thread to right
        elif direction == 'right':

            # Statistics
            self.__tree_header['stats']['threads to right'] += 1
            self.__save_header__( fd )

            # Find position in upper node
            pos = self.__binsearch__( giver['key'][-1], upper_node['key'] )

            # Thread key and data
            for par in ['key', 'data']:
                taker[par].insert( 0, upper_node[par][pos] )
                upper_node[par][pos] = giver[par].pop(-1)
                
            # If has lower nodes
            if len( giver['lower_node'] ) > 0:

                # Move pointer
                taker['lower_node'].insert( 0, giver['lower_node'].pop(-1) )
                
                # Fix left & right for node at offset=ptr
                sub = self.__load_node__( fd, taker['lower_node'][0] )
                sub['upper_node'] = taker['offset']
                sub['right_node'] = taker['lower_node'][1]
                sub['left_node'] = 0
                self.__save_node__( fd, sub )

                # Fix right for ex left node
                sub = self.__load_node__( fd, giver['lower_node'][-1] )
                sub['right_node'] = 0
                self.__save_node__( fd, sub )

                # Fix left for new right node
                sub = self.__load_node__( fd, taker['lower_node'][1] )
                sub['left_node'] = taker['lower_node'][0]
                self.__save_node__( fd, sub )
                
            ret = True

        # If ballanced
        if ret:

            # Save nodes
            for n in [taker, giver, upper_node]:
                self.__save_node__( fd, n )

            # Ballance taker if it's almost full to give room to next thread ballance.
            # This should keep occupation homogeneous across tree level
            if len(taker['key']) == ( self.__tree_header['num_keys'] - 1 ):
                self.__thread_ballance__( fd, taker['offset'] )
            
        return ret

    # ----------------------------------------------------------------------

    def check_consistency( self ):

        # Open b-tree file
        fd = open( self.__file_name, 'r+' )

        # Recursive check
        result = self.__check_consistency__( fd, self.__tree_header['root_offset'], 0, 0 )

        # Close file
        fd.close()

        if result == None:
            return False

        return True
    
    # ----------------------------------------------------------------------

    def __check_consistency__( self, fd, offset, left, right ):

        node = self.__load_node__( fd, offset )

        # Check for node overflow
        if len( node['key'] ) >= self.__tree_header['num_keys']:
            return None
            
        # Check for underflow in non-root nodes
        if len( node['key'] ) < self.__min_occup:
            if node['offset'] == self.__tree_header['root_offset']:
                return { 'min': 0, 'max': 0, 'upper_offset': 0 }
            else:
                print("Node em "+str(offset)+" tem = "+str(len( node['key'] ))+" nodes, quando num_keys = "+str(self.__tree_header['num_keys']))
                return None

        if node['left_node'] != left:
            print("Node em "+str(offset)+" pensa que left = "+str(node['left_node'])+", quanto na verdade left = "+str(left))
            return None

        if node['right_node'] != right:
            print("Node em "+str(offset)+" pensa que right = "+str(node['right_node'])+", quanto na verdade right = "+str(right))
            return None

        # Initialize max and min
        min_key = node['key'][-1]
        max_key = node['key'][0]
        
        # If not leaf
        if len( node['lower_node'] ) > 0:

            # Check how many lower nodes
            if len( node['lower_node'] ) != (len( node['key'] ) + 1):
                return None
            
            for i in range( len( node['key'] ) ):

                # Check left
                if i > 0:
                    _left = node['lower_node'][i-1]
                else:
                    _left = 0
                _right = node['lower_node'][i+1]
                left_consistency = self.__check_consistency__( fd, node['lower_node'][i], _left, _right )
                                
                # Check right
                _left = node['lower_node'][i]
                if i+1 < len(node['key']):
                    _right = node['lower_node'][i+2]
                else:
                    _right = 0
                right_consistency = self.__check_consistency__( fd, node['lower_node'][i+1], _left, _right )

                if left_consistency == None or right_consistency == None:
                    return None
                
                if left_consistency['upper_offset'] != offset or right_consistency['upper_offset'] != offset:
                    return None
                
                if left_consistency['max'] >= node['key'][i] or right_consistency['min'] <= node['key'][i] or node['key'][i] < max_key:
                    print('Inconsistency in node at offset='+str(node['offset'])+" ["+str(i)+"]")
                    print("Left offset = "+str(node['lower_node'][i]))
                    print("Max left  = '"+left_consistency['max']+"'")
                    print("Right offset = "+str(node['lower_node'][i+1]))
                    print("Min right = '"+right_consistency['min']+"'")
                    print("node: "+str(node['offset'])+": "+str(node['key']))
                    return None
                
                if left_consistency['min'] < min_key:
                    min_key = left_consistency['min']
                    
                if right_consistency['max'] > max_key:
                    max_key = right_consistency['max']

        # If leaf
        else:
            
            # If next key is not higher than current key, problem detected
            for i in range( len( node['key'] )- 1 ):
                if node['key'][i+1] <= node['key'][i]:
                    print('Inconsistency in node at offset='+str(node['offset']))
                    return None
            min_key = node['key'][0]
            max_key = node['key'][-1]
                
        return { 'min': min_key, 'max': max_key, 'upper_offset': node['upper_node'] }
    
    # ----------------------------------------------------------------------
    
    def __to_str__( self, obj ):

        if isinstance( obj, str ):
            return obj

        elif isinstance( obj, dict ) or isinstance( obj, list ):
            return json.dumps( obj )

        else:
            return str( obj )
    
    # ----------------------------------------------------------------------

    def __pop_max__( self, fd, offset ):

        # Load node
        node = self.__load_node__( fd, offset )
        
        # Load right-most lower node until it finds a leaf
        while len(node['lower_node']) > 0:
            node = self.__load_node__( fd, node['lower_node'][-1] )
            
        # Capture and remove right-most key and data
        max = { 'key': node['key'][-1], 'data':node['data'][-1], 'offset': node['offset'] }
        del node['key'][-1]
        del node['data'][-1]

        # Save node
        self.__save_node__( fd, node );

        # Return
        return max
        
    # ----------------------------------------------------------------------

    def stats( self ):
        return self.__tree_header['stats'].copy()
    
    # ----------------------------------------------------------------------

    def __move_node__( self, fd, old_offset, new_offset ):

        # Load nodes
        left_node = None
        right_node = None
        node = self.__load_node__( fd, old_offset )
        upper_node = self.__load_node__( fd, node['upper_node'] )
        if node['left_node'] > 0:
            left_node = self.__load_node__( fd, node['left_node'] )
        if node['right_node'] > 0:
            right_node = self.__load_node__( fd, node['right_node'] )
        
        # Find position in upper node
        pos = self.__binsearch__( node['key'][-1], upper_node['key'] )

        # Update pointers
        node['offset'] = new_offset
        upper_node['lower_node'][pos] = new_offset
        if node['left_node'] > 0:
            left_node['right_node'] = new_offset
        if node['right_node'] > 0:
            right_node['left_node'] = new_offset
        
        # Save nodes
        for n in [node, left_node, right_node, upper_node]:
            if n != None:
                self.__save_node__( fd, n )

        # Update lower nodes
        if len( node['lower_node'] ) > 0:
            for off in node['lower_node']:
                sub = self.__load_node__( fd, off )
                sub['upper_node'] = new_offset
                self.__save_node__( fd, sub )

    # ----------------------------------------------------------------------

    def __iter_check_end__( self, fd ):

        # If position is either before first key or after last key
        if self.__iter_pos == len( self.__iter_node['key'] ) or self.__iter_pos == -1:

            # If root, we're done
            if self.__iter_node['offset'] == self.__tree_header['root_offset']:
                self.__iter_dir = 'direct'
                raise ( StopIteration )
                                                                
            else:
                
                # Find next position in upper node
                min_key = self.__iter_node['key'][0]

                # Update iter
                self.__iter_node = self.__load_node__( fd, self.__iter_node['upper_node'] )
                self.__iter_pos = self.__binsearch__( min_key, self.__iter_node['key'] )
                
                if self.__iter_dir == 'reverse':
                    self.__iter_pos -= 1
                    
                # Check upwards
                self.__iter_check_end__( fd )
                    
    # ----------------------------------------------------------------------

    def __missing__(self, key):
        # Called by dict.__getitem__() to implement self[key] for dict subclasses when
        # key is not in the dictionary.

        raise KeyError(key)
        
    def __len__(self):
        # Called to implement the built-in function len(). Should return the length
        # of the object, an integer >= 0. Also, an object that doesn’t define a
        # __bool__() method and whose __len__() method returns zero is considered to
        # be false in a Boolean context.

        return int( self.__tree_header['stats']['keys'] )

    def __length_hint__(self):
        # Called to implement operator.length_hint(). Should return an estimated
        # length for the object (which may be greater or less than the actual
        # length). The length must be an integer >= 0. The return value may also
        # be NotImplemented, which is treated the same as if the __length_hint__
        # method didn’t exist at all. This method is purely an optimization and is
        # never required for correctness.

        return int( self.__tree_header['stats']['keys'] )

    def __getitem__(self, key):
        # Called to implement evaluation of self[key]. For sequence types, the
        # accepted keys should be integers and slice objects. Note that the special
        # interpretation of negative indexes (if the class wishes to emulate a
        # sequence type) is up to the __getitem__() method. If key is of an
        # inappropriate type, TypeError may be raised; if of a value outside the
        # set of indexes for the sequence (after any special interpretation of
        # negative values), IndexError should be raised. For mapping types, if key
        # is missing (not in the container), KeyError should be raised. Note for
        # loops expect that an IndexError will be raised for illegal indexes to
        # allow proper detection of the end of the sequence. Note When subscripting
        # a class, the special class method __class_getitem__() may be called
        # instead of __getitem__(). See __class_getitem__ versus __getitem__ for
        # more details.

        # Open b-tree file
        fd = open( self.__file_name, 'r' )

        # Search for key
        result = self.__rec_search__( fd, self.__tree_header['root_offset'], key )

        # Close file
        fd.close()

        # If not found, KeyError exception
        if not result['exists']:
            self.__missing__( key )

        # Return
        return result['node']['data'][result['position']]

    def __setitem__(self, key, value):
        # Called to implement assignment to self[key]. Same note as for __getitem__().
        # This should only be implemented for mappings if the objects support changes
        # to the values for keys, or if new keys can be added, or for sequences if
        # elements can be replaced. The same exceptions should be raised for improper
        # key values as for the __getitem__() method.

        #print("\nAdicionando: "+key+" ==> "+json.dumps(value))
        
        # Check value size
        if len( self.__to_str__( value ) ) > self.__max_data_size:
            raise ValueError("Value is too big. Limit is "+str(self.__max_data_size)+" bytes.")
        
        # Open b-tree file
        fd = open( self.__file_name, 'r+' )

        # Search for key
        result = self.__rec_search__( fd, self.__tree_header['root_offset'], key )

        # If found, update data
        if result['exists']:
            result['node']['data'][result['position']] = value

        # If not found, insert new pair key/data 
        else:
            result['node']['key'].insert( result['position'], key )
            result['node']['data'].insert( result['position'], value )
            # Statistics
            self.__tree_header['stats']['keys'] += 1
            self.__save_header__( fd )

        # Save node
        self.__save_node__( fd, result['node'] )

        # Ballance node
        if len(result['node']['key']) == self.__tree_header['num_keys']:
            if not self.__thread_ballance__( fd, result['node']['offset'] ):
                self.__split_node__( fd, result['node']['offset'] )

        # Close file
        fd.close()
        
    def __delitem__(self, key):
        # Called to implement deletion of self[key]. Same note as for __getitem__().
        # This should only be implemented for mappings if the objects support removal
        # of keys, or for sequences if elements can be removed from the sequence. The
        # same exceptions should be raised for improper key values as for the
        # __getitem__() method.

        # Open b-tree file
        fd = open( self.__file_name, 'r+' )

        # Search for key
        result = self.__rec_search__( fd, self.__tree_header['root_offset'], key )

        # If not found
        if not result['exists']:
            
            # Close file <-- Now, that's discipline!
            fd.close()
            
            # KeyError exception
            raise KeyError(key)

        # Statistics
        self.__tree_header['stats']['keys'] -= 1
        self.__save_header__( fd )

        
        # If not leaf
        if len( result['node']['lower_node'] ) > 0:

            # Replace deleted key with max key from left subtree
            max = self.__pop_max__( fd, result['node']['lower_node'][result['position']] )
            result['node']['key'][result['position']] = max['key']
            result['node']['data'][result['position']] = max['data']

            # Save node
            self.__save_node__( fd, result['node'] );

            # Ballance popped node which lost its max key
            popped = self.__load_node__( fd, max['offset'] )
            if len( popped['key'] ) < self.__min_occup:
                if not self.__thread_ballance__( fd, max['offset'] ):
                    self.__merge_node__( fd, max['offset'] )
            
        # If leaf
        else:
            
            # Remove
            del result['node']['key'][result['position']]
            del result['node']['data'][result['position']]

            # Save node
            self.__save_node__( fd, result['node'] );
        
        # Ballance node
        if len( result['node']['key'] ) < self.__min_occup:
            if not self.__thread_ballance__( fd, result['node']['offset'] ):
                self.__merge_node__( fd, result['node']['offset'] )

        # Close file
        fd.close()

    def __iter__(self):
        # This method is called when an iterator is required for a container. This
        # method should return a new iterator object that can iterate over all the
        # objects in the container. For mappings, it should iterate over the keys of
        # the container.

        # Open b-tree file
        fd = open( self.__file_name, 'r+' )

        # Load root
        self.__iter_node = self.__load_node__( fd, self.__tree_header['root_offset'] )

        # Find min leaf and set position
        while len( self.__iter_node['lower_node'] ) > 0:
            if self.__iter_dir == 'direct':
                self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][0] )
                self.__iter_pos=0
            else:
                self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][-1] )
                self.__iter_pos = len( self.__iter_node['key'] ) - 1

        # Close file
        fd.close()

        # Return
        return self
        
    def __next__(self):
        # This method is called when an iterator is required for a container. This
        # method should return a new iterator object that can iterate over all the
        # objects in the container. For mappings, it should iterate over the keys of
        # the container.

        # Open b-tree file
        fd = open( self.__file_name, 'r+' )

        # Check if reached end of key array
        self.__iter_check_end__( fd )

        # Capture Data
        result = self.__iter_node['key'][self.__iter_pos]

        # If leaf
        if len( self.__iter_node['lower_node'] ) == 0:

            if self.__iter_dir == 'direct':
                # Advance position
                self.__iter_pos += 1
            else:
                # Retreat position
                self.__iter_pos -= 1
        
        # If not leaf
        else:
            
            if self.__iter_dir == 'direct':
                
                # Load lower
                self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][self.__iter_pos+1] )

                # Find min leaf
                while len( self.__iter_node['lower_node'] ) > 0:
                    self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][0] )

                # Set position
                self.__iter_pos = 0
            else:

                # Load lower
                self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][self.__iter_pos] )

                # Find max leaf
                while len( self.__iter_node['lower_node'] ) > 0:
                    self.__iter_node = self.__load_node__( fd, self.__iter_node['lower_node'][-1] )

                # Set position
                self.__iter_pos = len( self.__iter_node['key'] ) - 1

        # Return
        return result
        
    def __reversed__(self):
        # Called (if present) by the reversed() built-in to implement reverse
        # iteration. It should return a new iterator object that iterates over all the
        # objects in the container in reverse order.
        # If the __reversed__() method is not provided, the reversed() built-in will
        # fall back to using the sequence protocol (__len__() and __getitem__()).
        # Objects that support the sequence protocol should only provide __reversed__()
        # if they can provide an implementation that is more efficient than the one
        # provided by reversed().
        # The membership test operators (in and not in) are normally implemented as an
        # iteration through a container. However, container objects can supply the
        # following special method with a more efficient implementation, which also
        # does not require the object be iterable.

        self.__iter_dir = 'reverse'
        return self

    def __contains__(self, item):
        # Called to implement membership test operators. Should return true if item is
        # in self, false otherwise. For mapping objects, this should consider the keys
        # of the mapping rather than the values or the key-item pairs.
        # For objects that don’t define __contains__(), the membership test first
        # tries iteration via __iter__(), then the old sequence iteration protocol via
        # __getitem__(), see this section in the language reference.

        # Open b-tree file
        fd = open( self.__file_name, 'r' )

        # Search for key
        result = self.__rec_search__( fd, self.__tree_header['root_offset'], item )

        # Close file
        fd.close()

        # Return
        return result['exists']

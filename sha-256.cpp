#include <iostream>
#include <string>
#include <vector>
#include <cmath>
#include <cstdint>

using namespace std;

enum direction
{
    left,
    right
};

uint32_t rotate_dword(uint32_t val, int digits, direction dir)
{
    if (dir == direction::right)
    {
        int mask_r = (1 << digits) - 1;
        int buf = val & mask_r;
        val = val >> digits;
        val = val | (buf << (32 - digits));
        return val;
    }
    else if (dir == direction::left)
    {
        unsigned int mask_l = ((1 << digits) - 1) << (32 - digits);
        int buf = (mask_l & val) >> (32 - digits);
        return (val << digits) | buf;
    }

    return 0;
}

uint32_t sigma_zero(uint32_t word)
{
    unsigned int part1 = rotate_dword(word, 7, direction::right);
    unsigned int part2 = rotate_dword(word, 18, direction::right);
    unsigned int part3 = word >> 3;
    return part1 ^ part2 ^ part3;
}

uint32_t sigma_one(uint32_t word)
{
    unsigned int part1 = rotate_dword(word, 17, direction::right);
    unsigned int part2 = rotate_dword(word, 19, direction::right);
    unsigned int part3 = word >> 10;
    return part1 ^ part2 ^ part3;
}

uint32_t sigma_zero_big(uint32_t word)
{
    unsigned int part1 = rotate_dword(word, 2, direction::right);
    unsigned int part2 = rotate_dword(word, 13, direction::right);
    unsigned int part3 = rotate_dword(word, 22, direction::right);
    return part1 ^ part2 ^ part3;
}

uint32_t sigma_one_big(uint32_t word)
{
    unsigned int part1 = rotate_dword(word, 6, direction::right);
    unsigned int part2 = rotate_dword(word, 11, direction::right);
    unsigned int part3 = rotate_dword(word, 25, direction::right);
    return part1 ^ part2 ^ part3;
}

uint32_t choose(uint32_t word1, uint32_t word2, uint32_t word3)
{
    return (word1 & word2) ^ (~word1 & word3);
}

uint32_t majority(uint32_t word1, uint32_t word2, uint32_t word3)
{
    return (word1 & word2) ^ (word1 & word3) ^ (word2 & word3);
}

vector<unsigned int> get_prime_numbers(unsigned int n)
{
    vector<unsigned int> prime_numbers;
    if (n >= 1)
    {
        prime_numbers.push_back(2);
    }
    int prime = 3;
    while (prime_numbers.size() < n)
    {
        int i = 2;
        while (true)
        {
            if (prime == i)
            {
                prime_numbers.push_back(prime);
                break;
            }
            else if (prime % i == 0)
            {
                break;
            }
            ++i;
        }
        ++prime;
    }
    return prime_numbers;
}

void create_constants_cube(vector<uint32_t> &vec)
{
    for (unsigned int i = 0; i < vec.size(); i++)
    {
        double x = pow(vec[i], (1.0 / 3.0));
        x = x - static_cast<uint32_t>(x);
        vec[i] = static_cast<uint32_t>(pow(2, 32) * x);
    }
}

void create_constants_square(vector<uint32_t> &vec)
{
    for (unsigned int i = 0; i < vec.size(); i++)
    {
        double x = pow(vec[i], 0.5);
        x = x - static_cast<uint32_t>(x);
        vec[i] = static_cast<uint32_t>(pow(2, 32) * x);
    }
}

vector<uint8_t> convert_string_to_int_array(string message){
    vector<uint8_t> x;
    for (unsigned int i = 0; i < message.length(); i++)
    {
        x.push_back(message[i]);
    }
    return x;
}

vector<uint32_t> create_message_block(vector<uint8_t> message){

    //message block needs to have a bit size of n * 512
    int msg_size = message.size()+9;
    int blocksize = msg_size/64.0;
    if (msg_size%64 != 0)
    {
        ++blocksize;
    }
    vector<uint32_t> message_block(16*blocksize);

    //writing 4 * 1 Byte messages into a 32_bit word, since calculations are made with 32_bit words
    for (int i = 0; i < message.size(); i++)
    {
        int j = i / 4;
        switch (i%4)
        {
        case 0:
            message_block[j] = (static_cast<uint32_t>(message[i]) << 24);
            break;
        case 1:
            message_block[j] |= (static_cast<uint32_t>(message[i]) << 16);
            break;
        case 2:
            message_block[j] |= (static_cast<uint32_t>(message[i]) << 8);
            break;
        case 3:
            message_block[j] |= message[i];
            break;
        default:
            break;
        }
    }

    //separator
    uint8_t separator_byte = 128;
    int x = message.size()/4;
    switch (message.size()%4)
    {
    case 0:
        message_block[x] = separator_byte << 24;
        break;
    case 1:
        message_block[x] |= separator_byte << 16;
        break;
    case 2:
        message_block[x] |= separator_byte << 8;
        break;
    case 3:
        message_block[x] |= separator_byte;
        break;
    default:
        break;
    }

    //64-bit big-endian-integer
    uint64_t ending = message.size()*8;
    message_block[message_block.size()] = static_cast<uint32_t>(ending >> 32);
    message_block[message_block.size()-1] = static_cast<uint32_t>(ending);

   return message_block;
}

vector<uint32_t> sha256(vector<uint32_t> initial_message_block){

    //k_constants stay's unchanged throughout the whole program
    vector<unsigned int> k_constants = get_prime_numbers(64);
    create_constants_cube(k_constants);
    //in this vector will be the final hash value. At first it will be assigned with the initial constants
    vector<uint32_t> working_variables_8 = get_prime_numbers(8);
    create_constants_square(working_variables_8);

    vector<uint32_t> prev_h(8);

    for (int i = 0; i < initial_message_block.size()/16; i++)
    {
        vector<uint32_t> working_v(64);

        for (int j = i*16; j < i*16 + 16; j++)
        {
            working_v[j-(i*16)] = initial_message_block[j];
        }

        //prepare message chunk for hash run-through
        for (int i = 0; i <= 47; i++)
        {
            uint32_t word4 = working_v[i];
            uint32_t word3 = sigma_zero(working_v[i+1]);
            uint32_t word2 = working_v[i+9];
            uint32_t word1 = sigma_one(working_v[i+14]);
            working_v[i+16] = static_cast<uint32_t>(word1 + word2 + word3 + word4);
        }

        //update working variables 
        for (int i = 0;  i < working_v.size(); i++)
        {
            uint32_t temp1 = choose(working_variables_8[4], working_variables_8[5], working_variables_8[6]);
            temp1 = static_cast<uint32_t>(working_variables_8[7] + sigma_one_big(working_variables_8[4]) + temp1 + k_constants[i] + working_v[i]);

            uint32_t temp2 = majority(working_variables_8[0], working_variables_8[1], working_variables_8[2]);
            temp2 = static_cast<uint32_t>(sigma_zero_big(working_variables_8[0]) + temp2);

            working_variables_8[7] = working_variables_8[6];
            working_variables_8[6] = working_variables_8[5];
            working_variables_8[5] = working_variables_8[4];
            working_variables_8[4] = static_cast<uint32_t>(working_variables_8[3] + temp1);
            working_variables_8[3] = working_variables_8[2];
            working_variables_8[2] = working_variables_8[1];
            working_variables_8[1] = working_variables_8[0];
            working_variables_8[0] = static_cast<uint32_t>(temp1+temp2);
        }

        if (i == 0)
        {
            vector<uint32_t> h = get_prime_numbers(8);
            create_constants_square(h);
            for (int i = 0; i < working_variables_8.size(); i++)
            {
                working_variables_8[i] += h[i];
            }
            prev_h = working_variables_8;
        }
        else{
            for (int i = 0; i < working_variables_8.size(); i++)
                {
                    working_variables_8[i] = prev_h[i] + working_variables_8[i];
                }
            prev_h = working_variables_8;
        }     
        
    }
    return working_variables_8;
}

int main()
{
    cout<<"Please Enter message to be hashed: ";
    string message;
    getline(cin, message);
    vector<uint32_t> initial_message_block = create_message_block(convert_string_to_int_array(message));
    vector<uint32_t> result = sha256(initial_message_block);
    
    cout<<"sha256: ";

    for (int i = 0; i < result.size(); i++)
    {
        cout<<hex<<result[i];
    }
    cout<<dec<<endl;

    return 0;
}
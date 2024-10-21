import json
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np

# Load the JSON data from file
data = []
with open('stats.json') as f:
    for l in f:
        r = json.loads(l)
        data.append({'kernelTime': r['kernel']['time'], 'lazyWhnfTime' : r['lazyWhnf']['time']})

# Convert the data into a pandas DataFrame
df = pd.DataFrame(data)

# Create a scatter plot with logarithmic axes
plt.figure(figsize=(8, 6))
plt.scatter(df['kernelTime'], df['lazyWhnfTime'], color='blue', marker='.', alpha=0.2)

# Add a straight line where lazyWhnfTime equals kernelTime (y = x)
ub = max(df['kernelTime'].max(), df['lazyWhnfTime'].max())
plt.axline((1000,1000), (ub,ub), color='grey')

# Set logarithmic scale for both axes
plt.xscale('log')
plt.yscale('log')

# Add labels and title
plt.xlabel('Kernel Time (ns)')
plt.ylabel('Lazy WHNF Time (ns)')
plt.title('Scatter Plot of Lazy WHNF Time vs Kernel Time (Log-Log Scale)')

print(df['kernelTime'].sum(), df['lazyWhnfTime'].sum())

#plt.show()
plt.savefig('plot.png')


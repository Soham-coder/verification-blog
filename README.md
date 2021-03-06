# Gatsby Starter Apple

[![Netlify Status](https://api.netlify.com/api/v1/badges/1407ade3-7666-4cab-a3e7-08380ce44735/deploy-status)](https://app.netlify.com/sites/gatsby-starter-apple/deploys)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Hits](https://hits.seeyoufarm.com/api/count/incr/badge.svg?url=https%3A%2F%2Fgithub.com%2Fsungik-choi%2Fgatsby-starter-apple&count_bg=%23FC2350&title_bg=%23555555&icon=gatsby.svg&icon_color=%23E7E7E7&title=HITS&edge_flat=false)](https://hits.seeyoufarm.com)

**Gatsby blog starter kit with beautiful responsive design**

![Screenshot](.github/screenshot.png)

## π Demo

π **View [Demo Page](https://gatsby-starter-apple.netlify.app/)**

## β¨ Features

- Lighthouse 100 + PWA
- styled-components
- Apple style responsive design
- Prefect dynamic theme (Comment + Code highlight)
- Beautiful mobile menu animation
- Code highlighting with [gatsby-remark-vscode](https://github.com/andrewbranch/gatsby-remark-vscode)
- [Utterances](https://utteranc.es/) Comment
- Categories support
- Infinite Scroll with Intersection Observer
- RSS Feed
- SEO
- Offline support
- Prettier & ESLint

## π Quick Start

### 1. Create a Gatsby site

Use the Gatsby CLI to create a new site, specifying the blog starter.

```shell
# create a new Gatsby site using the blog starter
gatsby new my-blog-starter https://github.com/sungik-choi/gatsby-starter-apple
```

### 2. Start developing

Navigate into your new siteβs directory and start it up.

```shell
cd my-blog-starter/
gatsby develop
```

### 3. Open the source code and start editing

Your site is now running at `http://localhost:8000`!

_Note: You'll also see a second link:_`http://localhost:8000/___graphql`_. This is a tool you can use to experiment with querying your data. Learn more about using this tool in the [Gatsby tutorial](https://www.gatsbyjs.com/tutorial/part-five/#introducing-graphiql)._

Open the `my-blog-starter` directory in your code editor of choice and edit `src/pages/index.js`. Save your changes and the browser will update in real time!

### 4. Fix meta data

Open **`gatsby-meta-config.js`** and fix meta data of your blog.

```js
module.exports = {
  title: 'Dev Ed', // Your website title
  description: `Ed's Blog`, // Your website description
  author: 'Ed', // Maybe your name
  siteUrl: 'https://gatsby-starter-apple.netlify.app', // Your website URL
  lang: 'en', // Language
  utterances: 'sungik-choi/gatsby-starter-apple-comment', // Github repository to store comments
  links: {
    github: 'https://github.com/sungik-choi/gatsby-starter-apple', // Your github repository
  },
  icon: 'src/images/icon.png', //  Favicon Path
};
```

## π€ What's Inside

```js
.
βββ node_modules
βββ src
β   βββ build
β   βββ components // React components
β   βββ constants
β   βββ hooks
β   βββ images
β   βββ layout
β   βββ pages
β   β   βββ index.js // Index page
β   β   βββ about.js // About page
β   β   βββ 404.js // 404 page
β   βββ posts
β   β   βββ blog
β   β   β   βββ images // Blog post images
β   β   β   βββ getting-started.md // Blog post markdown
β   β   β   βββ ...
β   β   βββ about.md // About page markdown
β   βββ store
β   βββ styles // Reusable styled components, animations
β   βββ templates
β   β   βββ blogPost.js // Blog post template
β   βββ utils
βββ .gitignore
βββ .eslintrc.js
βββ .prettierrc
βββ gatsby-meta-config.js // Gatsby meta data config
βββ gatsby-config.js // Gatsby config
βββ gatsby-node.js // Gatsby node config
βββ gatsby-ssr.js
βββ LICENSE
βββ package-lock.json
βββ package.json
βββ README.md
```

## π« Deploy

[![Deploy to Netlify](https://www.netlify.com/img/deploy/button.svg)](https://app.netlify.com/start/deploy?repository=https://github.com/sungik-choi/gatsby-starter-apple)
